from partitionsolver.partitioning.formula_splits import FormulaSplits
from partitionsolver.partitioning import hypergraph_edges_worker
import time
import numpy as np
import psutil
import lzma
from multiprocessing import Process, Queue
import multiprocessing as mp
from pysat.formula import CNF
import math

from collections import Counter, defaultdict

import pymetis
import igraph as ig

class DualGrapSplit(FormulaSplits):
    def __init__(self, file_location:str, splits_amount: int=2, cluster_type:str = 'edge_cuts'):
        '''
            Dual Graph: Vertices are clauses. Edge between vertices if clauses share variable
        '''
        self.splits_amount = splits_amount
        self.file_location = file_location
        self.cluster_type = cluster_type

        self.cut_variables = None

    def split_formula(self, clauses: list[list[int]], num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        # Per variable: List of clauses with that variable
        var_to_clauses = [[] for _ in range(num_variables)]
        for i in range(len(clauses)):
            for clause_var in [abs(l) for l in clauses[i]]:
                var_to_clauses[clause_var - 1].append(i)

        def get_metis_list():
            return self.build_metis_list(clauses, var_to_clauses, num_variables, num_clauses)

        def get_adj_matrix():
            return self.build_adj_matrix(clauses, var_to_clauses, num_variables, num_clauses)

        def get_adj_list():
            return self.build_adjacency_list(clauses, var_to_clauses, num_variables, num_clauses)
        
        if self.cluster_type == 'edge_cuts':
            return self.split_edge_cuts(clauses, get_metis_list(), num_variables, num_clauses)
        if self.cluster_type == 'community_leiden':
            return self.split_community_leiden(clauses, get_adj_list(), num_variables, num_clauses)
        if self.cluster_type == 'community_infomap':
            return self.split_community_infomap(clauses, get_adj_list(), num_variables, num_clauses)
        if self.cluster_type == 'community_walktrap':
            return self.split_community_walktrap(clauses, get_adj_list(), num_variables, num_clauses)
        else:
            raise NotImplementedError(f"Cluster type {self.cluster_type} is not implemented!")

    def split_edge_cuts(self, clauses: list[list[int]], adj_data, num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        xadj, adjncy, eweights = adj_data
        epsilon = 0.3
        ufactor = max(1, round(epsilon * 1000))
        options = pymetis.Options(ufactor=ufactor)
        n_cuts, membership = pymetis.part_graph(
            nparts=self.splits_amount, xadj=xadj, adjncy=adjncy, eweights=eweights, options=options
        )
        assert len(membership) == num_clauses
        return self.membership_to_split(membership, clauses, num_variables, num_clauses)


    def split_community_leiden(self, clauses: list[list[int]], adj_data, num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        edges, weights = adj_data
        g = ig.Graph(n=num_clauses, edges=edges)
        g.es['weight'] = weights

        # Dynamic amount of communities
        vertex_clustering = g.community_leiden(objective_function='modularity', weights='weight')
        membership = self.merge_to_k_clusters(g, vertex_clustering.membership)

        assert len(membership) == num_clauses
        return self.membership_to_split(membership, clauses, num_variables, num_clauses)

    def split_community_infomap(self, clauses: list[list[int]], adj_data, num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        edges, weights = adj_data
        g = ig.Graph(n=num_clauses, edges=edges)
        g.es['weight'] = weights

        # Dynamic amount of communities
        vertex_clustering = g.community_infomap(edge_weights='weight')
        membership = self.merge_to_k_clusters(g, vertex_clustering.membership)

        assert len(membership) == num_clauses
        return self.membership_to_split(membership, clauses, num_variables, num_clauses)

    def split_community_walktrap(self, clauses: list[list[int]], adj_data, num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        edges, weights = adj_data
        g = ig.Graph(n=num_clauses, edges=edges)
        g.es['weight'] = weights

        # Dynamic amount of communities
        vertex_dendrogram = g.community_walktrap(weights='weight')
        vertex_clustering = vertex_dendrogram.as_clustering()
        membership = self.merge_to_k_clusters(g, vertex_clustering.membership)

        assert len(membership) == num_clauses
        return self.membership_to_split(membership, clauses, num_variables, num_clauses)


    # === Convert CNF to graph in different representations ===
    def build_metis_list(self, clauses, var_to_clauses, num_variables, num_clauses):
        # dict-of-counters: neighbor_clause_idx -> shared_variable_count
        adjacency = [dict() for _ in range(num_clauses)]
        for clause in var_to_clauses:
            for i in range(len(clause)):
                for j in range(i + 1, len(clause)):
                    c1, c2 = clause[i], clause[j]
                    adjacency[c1][c2] = adjacency[c1].get(c2, 0) + 1
                    adjacency[c2][c1] = adjacency[c2].get(c1, 0) + 1

        xadj, adjncy, eweights = [0], [], []
        for i in range(num_clauses):
            for neighbor, weight in adjacency[i].items():
                adjncy.append(neighbor)
                eweights.append(weight)
            xadj.append(len(adjncy))
        return xadj, adjncy, eweights

    def build_adjacency_list(self, clauses, var_to_clauses, num_variables, num_clauses):
        adjacency = [dict() for _ in range(num_clauses)]
        for clause in var_to_clauses:
            for i in range(len(clause)):
                for j in range(i + 1, len(clause)):
                    c1, c2 = clause[i], clause[j]
                    adjacency[c1][c2] = adjacency[c1].get(c2, 0) + 1
                    adjacency[c2][c1] = adjacency[c2].get(c1, 0) + 1

        edges, weights = [], []
        for i in range(num_clauses):
            for j, w in adjacency[i].items():
                if j > i:  # avoid adding both directions
                    edges.append((i, j))
                    weights.append(w)

        return edges, weights

    def build_adj_matrix(self, clauses: list[list[int]], var_to_clauses, num_variables: int, num_clauses: int):
        adjaceny = np.zeros((num_clauses, num_clauses))
        for i in range(num_variables):
            connected_clauses = var_to_clauses[i]
            for k in range(len(connected_clauses)):
                for l in range(k + 1, len(connected_clauses)):
                    adjaceny[connected_clauses[k], connected_clauses[l]] += 1
                    adjaceny[connected_clauses[l], connected_clauses[k]] += 1
        return adjaceny


    # === Utility functions ===
    def membership_to_split(self, membership, clauses, num_variables: int, num_clauses: int):
        formulas = []
        p_clauses = [[] for _ in range(self.splits_amount)]
        used_variables = [[] for _ in range(self.splits_amount)]

        for i in range(num_clauses):
            p_clauses[membership[i]].append(clauses[i])
        
        for i in range(self.splits_amount):
            cnf = CNF(from_clauses=p_clauses[i])
            cnf.nv = num_variables
            formulas.append(cnf)

            used_variables[i] = [False] * num_variables
            for clause in p_clauses[i]:
                for l in clause:
                    used_variables[i][abs(l) - 1] = True

        var_usages = [0] * num_variables
        for i in range(num_variables):
            var_usages[i] = sum(1 if used_variables[j][i] else 0 for j in range(self.splits_amount))
        shared_vars = [i + 1 for i in range(num_variables) if var_usages[i] > 1]

        self.cut_variables = len(shared_vars)

        return formulas, shared_vars


    def merge_to_k_clusters(self, g, membership, weight_attr='weight'):
        membership = list(membership)

        while len(set(membership)) > self.splits_amount:
            cluster_a, cluster_b = self._find_merge_candidates(g, membership, weight_attr)
            membership = [cluster_a if c == cluster_b else c for c in membership]

        relabel = {old: new for new, old in enumerate(sorted(set(membership)))}
        return [relabel[c] for c in membership]


    def _find_merge_candidates(self, g, membership, weight_attr):
        mem_sizes = Counter(membership)
        largest_c = [c for c, _ in mem_sizes.most_common(self.splits_amount - 1)]

        weights_between = self._cluster_pair_weights(g, membership, weight_attr, largest_c)
        if weights_between:
            return max(weights_between, key=weights_between.get)

        # Fallback: merge smallest ones
        sizes = Counter(membership)
        smallest, second_smallest = sizes.most_common()[:-3:-1]
        return smallest[0], second_smallest[0]


    def _cluster_pair_weights(self, g, membership, weight_attr, largest_c):
        weights_between = defaultdict(int)
        for edge in g.es:
            c1 = membership[edge.source]
            c2 = membership[edge.target]
            if c1 == c2 or c1 in largest_c or c2 in largest_c:
                continue
            weight = edge[weight_attr] if weight_attr else 1
            weights_between[self._pair_key(c1, c2)] += weight
        return weights_between

    def _pair_key(self, cluster_a, cluster_b):
        return (cluster_a, cluster_b) if cluster_a < cluster_b else (cluster_b, cluster_a)

        