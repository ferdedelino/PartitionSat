from partitionsolver.partitioning.formula_splits import FormulaSplits
from partitionsolver.partitioning import hypergraph_edges_worker
import time
import numpy as np
import psutil
import lzma
from multiprocessing import Process, Queue
import multiprocessing as mp
from pysat.formula import CNF



class HyperGraphEdges(FormulaSplits):

    def __init__(self, file_location:str, splits_amount: int=2):
        self.splits_amount = splits_amount
        self.file_location = file_location

    def split_formula(self, clauses: list[list[int]], num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        # === Read in the hyperedges directly from file === 
        h_clauses, hyperedges = self.hypergraph_from_cnf_xz(file_location=self.file_location, display_progress=False, remove_empty_hyperedges=True)


        # === Compute a minimal split using multiprocessing === 
        ctx = mp.get_context("spawn")
        queue = ctx.Queue()
        p = Process(target=hypergraph_edges_worker.create_partition, args=(queue, h_clauses, hyperedges, self.splits_amount))
        p.start()
        result = queue.get()
        p.join()
        if p.exitcode != 0:
            print(f"Partitioning failed with exit code {p.exitcode} ({self.file_location})")
        del hyperedges
        partition = result["partition"]


        # === Extract clause lists from the partition ===
        formulas = []
        for i in range(self.splits_amount):
            c = [clause for clause, p in zip(clauses, partition) if p == i]
            formulas.append(c)

        # === Extract common variables ===
        comm_var_mask = [0] * num_variables
        for i in range(self.splits_amount):
            c = formulas[i]
            local_mask = [False] * num_variables
            for clause in c:
                for lit in clause:
                    local_mask[abs(lit) - 1] = True
            for j in range(num_variables):
                if local_mask[j]:
                    comm_var_mask[j] += 1

        common_variables = [i + 1 for i in range(num_variables) if comm_var_mask[i] >= 2]
        cnfs = []
        for i in range(self.splits_amount):
            cnf = CNF(from_clauses=formulas[i])
            cnf.nv = num_variables
            cnfs.append(cnf)

        return cnfs, common_variables


    
    def hypergraph_from_cnf_xz(self, file_location:str, display_progress:bool = False, remove_empty_hyperedges:bool = True):
        """Reads a .cnf or .cnf.xz file and creates a hypergraph representation of it."""

        start = time.perf_counter()
        opener = lzma.open if file_location.endswith(".xz") else open
        
        # First pass: count sizes
        num_vars = -1
        num_clauses = -1

        with opener(file_location, 'rt') as f:
            hyperedge_sizes = None
            for line in f:
                if line.startswith('%'):
                    break
                if line.startswith('c') or line.strip() == "":
                    continue
                if line.startswith('p'):
                    args = line.split()
                    num_vars = int(args[2])
                    num_clauses = int(args[3])
                    hyperedge_sizes = np.zeros(num_vars, dtype=int)
                    continue
                if num_vars == -1:
                    raise ValueError("Invalid CNF file: missing problem line")
                literals = line.split()
                for lit in literals:
                    if int(lit) == 0:
                        continue
                    var = abs(int(lit)) - 1
                    hyperedge_sizes[var] += 1

        if display_progress:
            print(f"Sizes counted in {time.perf_counter() - start:.2f}s")
            start = time.perf_counter()

        # Allocate
        hyperedges = np.empty(num_vars, dtype=object)
        hyperedge_indices = np.zeros(num_vars, dtype=int)
        for i in range(num_vars):
            hyperedges[i] = np.zeros(hyperedge_sizes[i], dtype=int)

        if display_progress:
            print(f"Memory allocated in {time.perf_counter() - start:.2f}s")
            print(f"Memory used: {psutil.virtual_memory().used / 1024**3:.2f} GB")
            start = time.perf_counter()

        # Second pass: fill
        with opener(file_location, 'rt') as f:
            clause_number = 0
            for line in f:
                if line.startswith('%'):
                    break
                if line.startswith('c') or line.startswith('p'):
                    continue
                for lit in line.split():
                    val = int(lit)
                    if val == 0:
                        continue
                    var = abs(val) - 1
                    hyperedges[var][hyperedge_indices[var]] = clause_number
                    hyperedge_indices[var] += 1
                clause_number += 1

        if display_progress:
            print(f"Edges filled in {time.perf_counter() - start:.2f}s")
            print(f"Memory used: {psutil.virtual_memory().used / 1024**3:.2f} GB")
            start = time.perf_counter()

        del hyperedge_indices  # free memory
    
        if not remove_empty_hyperedges:
            del hyperedge_sizes  # free memory
            return num_clauses, hyperedges

        mask = hyperedge_sizes > 0
        del hyperedge_sizes  # free memory
        cleaned_hyperedges = hyperedges[mask]
        del hyperedges  # free memory

        if display_progress:
            print(f"Hyperedges cleaned in {time.perf_counter() - start:.2f}s")
        
        return num_clauses, cleaned_hyperedges
