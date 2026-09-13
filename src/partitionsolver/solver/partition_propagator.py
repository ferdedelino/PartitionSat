import time
from typing import List, Optional

from pysat.solvers import Cadical195
from pysat.solvers import Cadical300
from pysat.solvers import Mergesat3
from pysat.engines import Propagator
from pysat.formula import CNF

from partitionsolver.solver.partition_solver_cdcl import PartitionCDCL
from partitionsolver.utils import literal_util

import concurrent.futures
import time
from typing import List
import threading
import queue


class PartitionPropagator(Propagator):
    def __init__(self, num_variables: int, glue_variables: List[int],
                 partial_formulas: List[CNF], debug_level: int = 0, parallel = False):
        self.num_variables = num_variables
        self.glue_variables = set(glue_variables)
        self.partial_formulas = partial_formulas
        self.solver = None
        self.oracles = self._initialize_persistent_solvers()

        # one list of glue-vars assigned per decision level; level_trail[0]
        # holds root-level (fixed) assignments
        self.level_trail = [[]]
        self.forced_variable = self.num_variables + 1
        self.assignment = {}          # glue var -> bool, current partial assignment
        self.dirty = False            # did the glue assignment change since last check?

        self.pending_clause = None
        self.model_reject_clause = None

        self.DEBUG_LEVEL = debug_level
        self.test_time = 0.0
        self.num_checks = 0
        self.num_partial_checks = 0
        self.num_model_checks = 0
        self.added_reasons = 0

        self.add_seed_clauses = False
        self.add_seed_clauses_amount = -1
        self.parallel = parallel

        self.model = None

        self.clauses_to_add = []
        self.secondary_clauses_to_add = []
        self.pending_level_0_decisions = []

        # Configuration
        self.clauses_add_intervall = 100
        self.clauses_add_per_intervall = 10
        self.secondary_clauses_add_intervall = 200
        self.secondary_clauses_add_per_intervall = 10


        # Visualization
        self.seed_clauses_size = []
        

    def solve(self):
        if self.add_seed_clauses:
            amount = self.add_seed_clauses_amount
            if amount == -1:
                amount = int(self.num_variables * 2)
            decided_sat, result = self.generate_seed_clauses(amount=amount)
            if decided_sat:
                return result
            seed_clauses = result # result type depends in first argument
            
        else:
            seed_clauses = []
        for solver in self.oracles:
            solver.append_formula(seed_clauses)


        seed_clauses.append([self.forced_variable])

        # Use version 195, newer versions run unstable with external propagators.
        self.solver = Cadical195(bootstrap_with=CNF(from_clauses=seed_clauses))
        self.solver.connect_propagator(self)
        for v in self.glue_variables:
            self.solver.observe(v)

        sat = self.solver.solve()
        if sat:
            self.model = self.solver.get_model()

        # Throws errors in Cadical300
        #solver.delete()
        #for o in self.oracles:
        #    o.delete()

        return sat

    def _initialize_persistent_solvers(self):
        oracles = []
        for cnf in self.partial_formulas:
            cnf.nv = self.num_variables
            oracles.append(Cadical300(bootstrap_with=cnf))

        return oracles


    # ------------------------------------------------------------------ #
    # IPASIR-UP callbacks
    # ------------------------------------------------------------------ #

    def on_assignment(self, lit: int, fixed: bool = False) -> None:
        v = abs(lit)
        if v in self.glue_variables:
            self.assignment[v] = lit > 0
            self.level_trail[-1].append(v)
            self.dirty = True
            if len(self.level_trail) == 1 or fixed:
                self.pending_level_0_decisions.append(lit)
                #print(f"Level 0 prop: {lit}")

    def on_new_level(self) -> None:
        self.level_trail.append([])

    def on_backtrack(self, to: int) -> None:
        while len(self.level_trail) - 1 > to:
            for v in self.level_trail.pop():
                self.assignment.pop(v)
        if not self.level_trail:
            self.level_trail = [[]]
        self.dirty = True
        self.pending_clause = None

    def decide(self) -> int:
        return 0  # let the solver pick decisions itself

    def propagate(self) -> List[int]:
        # called at every BCP fixpoint; only re-run oracles if something about the glue assignment actually changed, and only if we don't already have a clause queued up
        assumptions = [var if value else -var for var, value in self.assignment.items()]

        if not self.dirty and self.pending_clause is None:
            return []
        self.dirty = False
        sat, core = self._test(assumptions, partial=True)
        if not sat:
            if len(assumptions) == 0 or core is None:
                #print("CONFLICT")
                self.pending_clause = [] # unsat with no assumptions: unsat
            else:
                if core is None:
                    #print("Core is None???")
                    #print("CONFLICT")
                    self.pending_clause = []
                else:
                    self.pending_clause = [-l for l in core]
            return [-self.forced_variable]
            
        return []

    def provide_reason(self, lit: int) -> List[int]:
        clause = self.pending_clause.copy()
        clause.append(-self.forced_variable)
        self.pending_clause = None
        self.added_reasons += 1
        #if self.solver.nof_clauses() % 30 == 0:
        #    print(self.solver.nof_clauses())
        #print("test2")
        return clause

    def has_clause(self) -> bool:
        return self.model_reject_clause is not None
 
    def add_clause(self) -> List[int]:
        clause, self.model_reject_clause = self.model_reject_clause, None
        return clause if clause else []
 
    def check_model(self, model: List[int]) -> bool:
        # Checking a fully assigned model
        assumptions = [l for l in model if abs(l) in self.glue_variables]
        assert len(assumptions) == len(self.glue_variables), f"Got {len(assumptions)}, expected {len(self.glue_variables)}"
        sat, core = self._test(assumptions, partial=False)
        if sat:
            return True

        if core is None:
            core = assumptions
        self.model_reject_clause = [-l for l in core]

        return False




    # ------------------------------------------------------------------ #
    # Custom methods
    # ------------------------------------------------------------------ #

    def _test(self, assumptions: List[int], partial: bool):
        self.share_level_0_decisions() # Variables propagated as "fixed" are 
        start = time.perf_counter()
        sat, core = True, None
        oracle_number = 0
        for i in range(len(self.oracles)):
            solver = self.oracles[i]
            if not solver.solve(assumptions=assumptions):
                oracle_number = i
                sat = False
                core = solver.get_core()
                break

        if oracle_number != 0 and not core is None:
            self.clauses_to_add.append([-l for l in core])
            if len(self.clauses_to_add) > self.clauses_add_intervall:
                clauses = []
                added = 0
                for clause in sorted(self.clauses_to_add, key=len):
                    if len(clause) > 2 and added >= self.clauses_add_per_intervall:
                        break
                    clauses.append(clause)
                    added += 1
                self.oracles[0].append_formula(clauses)
                self.clauses_to_add = []

        if oracle_number == 0 and not core is None:
            self.secondary_clauses_to_add.append([-l for l in core])
            if len(self.secondary_clauses_to_add) > self.secondary_clauses_add_intervall:
                clauses = []
                added = 0
                for clause in sorted(self.secondary_clauses_to_add, key=len):
                    if len(clause) > 2 and added >= self.secondary_clauses_add_per_intervall:
                        break
                    clauses.append(clause)
                    added += 1
                for oracle in self.oracles[1:]:
                    oracle.append_formula(clauses)
                self.secondary_clauses_to_add = []

        elapsed = time.perf_counter() - start
        self.test_time += elapsed
        self.num_checks += 1
        self.num_partial_checks += partial
        self.num_model_checks += not partial

        #if not partial and sat:
        #    print("All solver say satisfiable!")

        return sat, core

    def share_level_0_decisions(self):
        if len(self.pending_level_0_decisions) == 0:
            return
        for solver in self.oracles:
            solver.append_formula([[l] for l in self.pending_level_0_decisions])
        self.pending_level_0_decisions = []

    def print_infos(self):
        print(f" === INFORMATION === ")
        print(f"  test_time: {1000 * (self.test_time):.2f}")
        if self.add_seed_clauses:
            print(f"  seed_clauses_time: {1000 * (self.seed_clauses_time):.2f}")
        print(f"  num_checks: {self.num_checks}")
        print(f"  num_partial_checks: {self.num_partial_checks}")
        print(f"  num_model_checks: {self.num_model_checks}")
        print(f"  added_reasons: {self.added_reasons}")
        if self.solver != None:
            print(f"  Number of internal clauses: {self.solver.nof_clauses()}")

    def generate_seed_clauses(self, amount):
        start = time.perf_counter()
        cdcl_solver = PartitionCDCL(self.num_variables, sorted([var for var in self.glue_variables]), [f.clauses for f in self.partial_formulas], self.DEBUG_LEVEL, solvers=self.oracles)
        cdcl_solver.reset_solver()
        
        max_initial_amount = amount
        learnt_lengths = []
        window = 10
        cutoff_size = 2.8
        def stop_condition(clause_len):
            learnt_lengths.append(clause_len)
            if len(learnt_lengths) < window:
                return False
            if sum(learnt_lengths[-window:]) > cutoff_size * window:
                return True
            return False

        found_result_while_probing = cdcl_solver.add_initial_clauses(max_initial_amount, stop_condition)
        if found_result_while_probing is not None:
            if found_result_while_probing:
                self.model = cdcl_solver.model
            self.seed_clauses_time = time.perf_counter() - start
            return True, found_result_while_probing

        seed_clauses = []
        for bin_clause in cdcl_solver.learnt_clauses:
            seed_clauses.append(literal_util.clause_to_dimacs(bin_clause))
        global_decision_vars = {index for index, _ in cdcl_solver.trails[0]}
        for var_index in global_decision_vars:
            var = cdcl_solver.glue_variables[var_index]
            unit_clause = [var] if cdcl_solver.values[var_index] > 0 else [-var]
            seed_clauses.append(unit_clause)
            self.pending_level_0_decisions.append(var if cdcl_solver.values[var_index] > 0 else -var)

        self.seed_clauses_time = time.perf_counter() - start
        self.seed_clauses_size = [len(clause) for clause in seed_clauses]
        return False, seed_clauses