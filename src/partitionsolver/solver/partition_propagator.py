import time
from typing import List, Optional

from pysat.solvers import Cadical195
from pysat.solvers import Cadical300
from pysat.engines import Propagator
from pysat.formula import CNF

from partitionsolver.solver.partition_solver_cdcl import PartitionCDCL
from partitionsolver.utils import literal_util


class PartitionPropagator(Propagator):
    def __init__(self, num_variables: int, glue_variables: List[int],
                 partial_formulas: List[CNF], debug_level: int = 0):
        self.num_variables = num_variables
        self.glue_variables = set(glue_variables)
        self.partial_formulas = partial_formulas
        self.oracles = self._initialize_persistent_solvers()

        # one list of glue-vars assigned per decision level; level_trail[0]
        # holds root-level (fixed) assignments
        self.level_trail = [[]]
        self.assignment = {}          # glue var -> bool, current partial assignment
        self.dirty = False            # did the glue assignment change since last check?

        self.pending_clause = None

        self.DEBUG_LEVEL = debug_level
        self.test_time = 0.0
        self.num_checks = 0
        self.num_partial_checks = 0
        self.num_model_checks = 0

        self.add_seed_clauses = False

        self.model = None


    def solve(self):
        if self.add_seed_clauses:
            decided_sat, result = self.generate_seed_clauses(amount=int(self.num_variables * 0))
            if decided_sat:
                return result
            seed_clauses = result # result type depends in first argument
        else:
            seed_clauses = []
        
        # Only Cadical195 supports Propagators
        solver = Cadical195(bootstrap_with=CNF(from_clauses=seed_clauses))
        solver.connect_propagator(self)
        for v in self.glue_variables:
            solver.observe(v)

        sat = solver.solve()
        if sat:
            self.model = solver.get_model()

        solver.delete()
        for o in self.oracles:
            o.delete()

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
        if self.dirty and self.pending_clause is None:
            self.dirty = False
            assumptions = [var if value else -var for var, value in self.assignment.items()]
            sat, core = self._test(assumptions, partial=True)
            if not sat:
                if len(assumptions) == 0:
                    self.pending_clause = [] # unsat with no assumptions: unsat
                else:
                    self.pending_clause = [-l for l in core]

        # If sat, we could extract implications from the oracles. But for now don't propagate any variables
        # TODO: Cadical 3.0 lets you extract implications from an assumptions run.
        return []

    def provide_reason(self, lit: int) -> List[int]:
        # unused for now, see the TODO above
        return []

    def has_clause(self) -> bool:
        return self.pending_clause is not None

    def add_clause(self) -> List[int]:
        clause = self.pending_clause
        self.pending_clause = None
        return clause if clause else [1, -1] # Default: tautological clause - gets ignored

    def check_model(self, model: List[int]) -> bool:
        # Checking a fully assigned model
        assumptions = [l for l in model if abs(l) in self.glue_variables]
        sat, core = self._test(assumptions, partial=False)
        if sat:
            return True
        self.pending_clause = [-l for l in core]
        return False



    # ------------------------------------------------------------------ #
    # Custom methods
    # ------------------------------------------------------------------ #

    def _test(self, assumptions: List[int], partial: bool):
        start = time.perf_counter()
        sat, core = True, None
        for solver in self.oracles:
            if not solver.solve(assumptions=assumptions):
                sat = False
                core = solver.get_core()
                break
        elapsed = time.perf_counter() - start
        self.test_time += elapsed
        self.num_checks += 1
        self.num_partial_checks += partial
        self.num_model_checks += not partial

        return sat, core

    def generate_seed_clauses(self, amount):
        start = time.perf_counter()
        cdcl_solver = PartitionCDCL(self.num_variables, sorted([var for var in self.glue_variables]), [f.clauses for f in self.partial_formulas], self.DEBUG_LEVEL)
        cdcl_solver.reset_solver()
        cdcl_solver.initialize_persistent_solvers()
        
        initial_clauses_amount = amount
        found_result_while_probing = cdcl_solver.add_initial_clauses(initial_clauses_amount)
        if found_result_while_probing is not None:
            if found_result_while_probing:
                self.model = cdcl_solver.model
            return True, found_result_while_probing

        seed_clauses = []
        for bin_clause in cdcl_solver.learnt_clauses:
            seed_clauses.append(literal_util.clause_to_dimacs(bin_clause))
        global_decision_vars = {index for index, _ in cdcl_solver.trails[0]}
        for var_index in global_decision_vars:
            var = cdcl_solver.glue_variables[var_index]
            unit_clause = [var] if cdcl_solver.values[var_index] > 0 else [-var]
            seed_clauses.append(unit_clause)

        self.seed_clauses_time = time.perf_counter() - start
        return False, seed_clauses