from operator import index
import random
from pysat.solvers import Cadical300
from pysat.formula import CNF
import time

from partitionsolver.solver.two_watched_literals import TwoWatchedLiterals
from partitionsolver.solver.variable_translation import VariableTranslation
from partitionsolver.solver.variable_selection import VariableSelector
from partitionsolver.utils import literal_util
from partitionsolver.utils.clause_allocator import ClauseAllocator
from partitionsolver.utils.heapdict import HeapDict


class PartitionCDCL:

    def __init__(self, num_variables:int, glue_variables:list, partial_clauses:list, debug_level:int = 0):
        self.num_variables = num_variables
        self.glue_variables = glue_variables
        self.partial_clauses = partial_clauses
        self.num_gvars = len(glue_variables)
        self.DEBUG_LEVEL = debug_level

        self.trails = [] # (variable_index, antecedent)
        self.values = [0] * self.num_gvars
        self.variable_levels = [-1] * self.num_gvars # -1: not set, 0: globally set

        self.var_to_index = {var: index for index, var in enumerate(glue_variables)}

        self.learnt_clauses = ClauseAllocator() # Learnt clauses, in bitshifted variable format - NOT DIMACS
        self.var_activity = [0] * self.num_gvars
        #    clause_activity handled in self.learnt_clauses: ClauseAllocator
        self.variable_selector = VariableSelector(self.glue_variables)
        self.variable_heap = HeapDict()
        self.variable_polarity = [False] * self.num_gvars


        self.twl_translation = VariableTranslation(glue_variables)
        self.two_watched_literals = TwoWatchedLiterals(self.num_gvars, {clause_id: self.twl_translation.clause_to_local(clause) for clause_id, clause in self.learnt_clauses.items()}, base_clauses_in_dimacs=False)

        self.luby_restarts = False
        self.restarts_first = 100
        self.restart_inc = 2 if self.luby_restarts else 1.5

        self.nof_prop_conflicts = 0
        self.nof_test_conflicts = 0
        self.nof_implications = 0
        self.test_time = 0

        self.var_incr = 1                 # Helper variable to regulate variable activity
        self.clause_incr = 1              # Helper variable to regulate clause activity
        self.var_decay = 0.95             # How much variable activity decays every conflict
        self.clause_decay = 0.999         # How much clause activity decaus every conflict
        self.learntsize_factor = 5        # Initial amount of learnt clauses, as a factor of # of glue variables
        self.learntsize_inc = 1.1         # How much the learnt clause limit grows with every restart
        self.max_learnts = 0              # Limit of learnt clauses - increases during solve
        self.min_learnts_lim = 2          # Minimum number of limit to learnt clauses

        self.learntsize_adjust_cnt = 1
        self.learntsize_adjust_inc = 1.5
        self.learntsize_adjust_confl = 100
        self.learntsize_adjust_cnt = self.learntsize_adjust_confl

        self.solution = None

    def solve(self):
        self.reset_solver()
        self.initialize_persistent_solvers()

        self.max_learnts = self.num_gvars * self.learntsize_factor
        if (self.max_learnts < self.min_learnts_lim):
            self.max_learnts = self.min_learnts_lim


        # Warmup
        start = time.perf_counter()
        initial_clauses_amount = max(int(self.max_learnts / 2), self.num_gvars * 2)
        found_result_while_probing = self.add_initial_clauses(initial_clauses_amount)
        if self.DEBUG_LEVEL >= 1:
            print(f"Finished adding initial clauses in {1000 * (time.perf_counter() - start):.2f}ms")
            clause_len_median = sorted([len(clause) for clause in self.learnt_clauses])[len(self.learnt_clauses) // 2] if len(self.learnt_clauses) > 0 else 0
            clause_len_mean = sum([len(clause) for clause in self.learnt_clauses]) / len(self.learnt_clauses) if len(self.learnt_clauses) > 0 else 0
            print(f"Initial clauses: {len(self.learnt_clauses)}, median length: {clause_len_median}, mean length: {clause_len_mean:.2f}")
        if found_result_while_probing is not None:
            #self.model = ... is set in add_initial_clauses()
            return found_result_while_probing
        self.set_initial_var_activity()

        curr_restarts = 0
        restart_increment = 1
        while True:
            if not self.luby_restarts:
                restart_base = int(self.restarts_first * restart_increment)
                restart_increment *= self.restart_inc
            else:
                restart_base = int(self.restarts_first * self.luby_sequence(self.restart_inc, curr_restarts))
        
            curr_restarts += 1

            nof_test_conflicts_start = self.nof_test_conflicts
            nof_prop_conflicts_start = self.nof_prop_conflicts
            nof_implications_start = self.nof_implications
            test_time = self.test_time
            start_time = time.perf_counter()

            self.reset_solver()

            # ======
            found_model = self.search(restart_base)
            if found_model is not None:
                return found_model
            # ======
            
            # Max number of conflicts reached
            prop_conflicts = self.nof_prop_conflicts - nof_prop_conflicts_start
            test_conflicts = self.nof_test_conflicts - nof_test_conflicts_start
            implications = self.nof_implications - nof_implications_start
            total_time = time.perf_counter() - start_time
            test_time = self.test_time - test_time
            if self.DEBUG_LEVEL >= 2:
                print(f"Restart {curr_restarts} after {restart_base} conflicts. Conflicts: {prop_conflicts} prop conflicts + {test_conflicts} test conflicts. Propagations: {implications}. Times: {1000 * total_time:.2f}ms total - {1000 * test_time:.2f}ms test time")


    def test_assignment(self):
        start = time.perf_counter()
        assumption_lits = [self.glue_variables[var_index] * (-1 if value < 0 else 1) for var_index, value in enumerate(self.values) if value != 0]

        #TODO: which order?
        sat = True
        conflict_core = None
        for solver in self.persistant_solvers:
            if not solver.solve(assumptions=assumption_lits):
                sat = False
                conflict_core = solver.get_core()
                break

        if self.DEBUG_LEVEL >= 3:
            print(f"Tested single assignment in {1000 * (time.perf_counter() - start):.2f}ms")

        self.test_time += time.perf_counter() - start
        return sat, conflict_core

    def local_clauses_cause_conflict(self):
        for clause in self.learnt_clauses:
            conflict = True
            for lit in clause:
                var = literal_util.get_variable(lit)
                var_index = self.var_to_index[var]
                value = self.values[var_index]
                if value == 0:
                    conflict = False
                    break
                if literal_util.is_negative(lit) and value < 0:
                    conflict = False
                    break
                if literal_util.is_positive(lit) and value > 0:
                    conflict = False
                    break
            if conflict:
                return True
        return False

    def initialize_persistent_solvers(self):
        # Destroy old instances (maybe a todo for later - keeping them?)
        for solver in getattr(self, 'persistant_solvers', []) or []:
            if solver is not None:
                solver.delete()
            self.persistant_solvers = []

        # Create solvers that support assumptions!
        self.persistant_solvers = [None] * len(self.partial_clauses)
        for i in range(len(self.partial_clauses)):
            clauses = self.partial_clauses[i]
            cnf = CNF(from_clauses=clauses)
            cnf.nv = self.num_variables
            self.persistant_solvers[i] = Cadical300(bootstrap_with=cnf)

    
    def reset_solver(self, keep_global_decisions:bool = True, keep_learnt_clauses = True):
        self.decision_level = 0
        self.decision_stack = []
        self.variable_levels = [-1] * self.num_gvars

        #TODO: rewrite this

        if keep_global_decisions:
            if len(self.trails) >= 1:
                self.trails = self.trails[0:1]
                global_decision_vars = {index for index, _ in self.trails[0]}
            else:
                self.trails = [[]]
                global_decision_vars = {}
        else:
            self.trails = [[]]
            global_decision_vars = []

        if len(global_decision_vars) == 0:
            self.values = [0] * self.num_gvars
        else:
            self.values = [old_value if i in global_decision_vars else 0 for i, old_value in enumerate(self.values)]
            for vi in global_decision_vars:
                self.variable_levels[vi] = 0

        if not keep_learnt_clauses:
            self.learnt_clauses.reset()

        self.variable_heap.clear()
        for vi in range(self.num_gvars):
            if not vi in global_decision_vars:
                self.variable_heap[vi] = -self.var_activity[vi]

        
        self.two_watched_literals = TwoWatchedLiterals(self.num_gvars, {}, base_clauses_in_dimacs=False)
        for clause_id, clause in self.learnt_clauses.items():
            self.two_watched_literals.add_learnt_clause(self.twl_translation.clause_to_local(clause), clause_id, self.values)

    
    def all_variables_set(self):
        #return self.variable_selector.all_variables_set(self.values)
        return len(self.variable_heap) == 0

    def next_decision(self):
        #return self.variable_selector.next_decision(self.values)

        #expected = self.num_gvars - self.decision_level
        #for trail in self.trails:
        #    expected -= len(trail)
        #assert len(self.variable_heap) == expected, f"Got length {len(self.variable_heap)}, expected {self.num_gvars - self.decision_level}"
        next_var_index = self.variable_heap.popitem()[0]
        return next_var_index, self.variable_polarity[next_var_index]

    def set_initial_var_activity(self):
        activity_scores_pos = [0] * self.num_gvars
        activity_scores_neg = [0] * self.num_gvars
        
        for clause in self.learnt_clauses:
            for lit in clause:
                var = literal_util.get_variable(lit)
                var_index = self.var_to_index[var]
        
                if literal_util.is_positive(lit):
                    activity_scores_pos[var_index] += 1/(2**len(clause))
                else:
                    activity_scores_neg[var_index] += 1/(2**len(clause))
        
        total_activity = [
            [pos, False] if pos > neg else [neg, True]
            for pos, neg in zip(activity_scores_pos, activity_scores_neg)
        ]
        #median_activity = sorted([activity for activity, _ in total_activity])[len(total_activity) // 2] if len(total_activity) > 0 else 0
        for i in range(len(total_activity)):
            total_activity[i][0] = total_activity[i][0] + total_activity[i][0] * ((random.random() - 0.5) * 0.3)
                    
        #self.variable_selector.sort_variables_by_activity(total_activity)
        for variable_index in range(self.num_gvars):
            if self.variable_levels[variable_index] == 0:
                continue
            self.variable_heap[variable_index] = -total_activity[variable_index][0]
            self.variable_polarity[variable_index] = total_activity[variable_index][1]
    
    def backtrack(self, decision_level_target:int):
        """ Resets the state of the solver to the given decision level.
            The assignment of decision_level_target are NOT changed, only assignments above that level! 
        """
        assert decision_level_target <= self.decision_level
        while self.decision_level > decision_level_target:
            for trail_variable_index, antecedent in self.trails[self.decision_level]:
                self.variable_levels[trail_variable_index] = -1
                self.learnt_clauses.set_locked(antecedent, False)
                self.variable_heap[trail_variable_index] = -self.var_activity[trail_variable_index]
                self.variable_polarity[trail_variable_index] = self.values[trail_variable_index] > 0
                self.values[trail_variable_index] = 0
            self.trails.pop()

            # Reset the decision variable of the current decision level
            variable, variable_index = self.decision_stack[self.decision_level - 1]
            self.variable_levels[variable_index] = -1
            self.decision_stack.pop()
            self.variable_heap[variable_index] = -self.var_activity[variable_index]
            self.variable_polarity[variable_index] = self.values[variable_index] > 0
            self.values[variable_index] = 0

            self.decision_level -= 1
        
        assert self.decision_level == decision_level_target
        assert len(self.decision_stack) == self.decision_level, f"decision_stack {len(self.decision_stack)}, decision_level {self.decision_level}"
        assert len(self.trails) == self.decision_level + 1

    def unit_propagate(self, decision_var, decision_var_index, decision_value):
        """ Applies unit propagation to the given decided variable and applies all implications.
            Returns False if conflict, True otherwise.
            If conflict occurs (return False), the caller has to backtrack themselves!.
        """
        assert self.values[decision_var_index] == decision_value
        assert decision_value != 0
        assert len(self.trails) == self.decision_level + 1, f"Got len trails of {len(self.trails)} on decision level {self.decision_level}"

        trail = self.trails[self.decision_level]
        initial_trail_length = len(trail)

        def reset_propagations():
            return # I think this is unnecesary, will be done in #backtrack anyways
            for i in range(initial_trail_length, len(trail)):
                var_index, _ = trail[i]
                self.values[var_index] = 0
                self.variable_levels[var_index] = -1
            self.trails[self.decision_level] = trail[0:initial_trail_length]

        def notify_false(var, var_index, value):
            assert value != 0
            twl_lit = literal_util.get_neg_lit(var) if value > 0 else literal_util.get_pos_lit(var)
            
            twl_forced_literals, twl_sat, twl_conflict_clause = self.two_watched_literals.notify_false(
                self.twl_translation.lit_to_local_name(twl_lit),
                self.values
            )
            twl_forced_literals = [(self.twl_translation.lit_to_global_name(l), antecedent) for l, antecedent in twl_forced_literals]
            return twl_forced_literals, twl_sat, twl_conflict_clause
        
        forced_initial_literals, initial_satisfiable, initial_conflict_clause = notify_false(decision_var, decision_var_index, decision_value)
        
        if not initial_satisfiable:
            #print(f"Initial Unit prop unsat: {conflict_clause}")
            return False, initial_conflict_clause
        
        propagated = [(lit, antecedent) for (lit, antecedent) in forced_initial_literals]
        while len(propagated) > 0:
            unit, antecedent = propagated.pop()
            assert unit != 0
            variable = literal_util.get_variable(unit)
            var_index = self.var_to_index[variable]

            # variable is already set. Two options: Set to same value, or conflict
            old_value = self.values[var_index]

            if old_value != 0:
                correct = (literal_util.is_positive(unit) and old_value > 0) or \
                          (literal_util.is_negative(unit) and old_value < 0)
                if not correct:
                    #assert self.test_assignment()[0] == False
                    reset_propagations()
                    assert True == False
                    print("No conflict clause - unse antecedent instead")
                    return False, antecedent # ???? #TODO: Can you treat the antecedent as a conflict clause?
                continue
            
            new_value = 1 if literal_util.is_positive(unit) else -1
            self.enqueue(var_index, new_value, antecedent, trail)

            self.nof_implications += 1

            # Add next units implied by this assignment
            forced_literals, satisfiable, conflict_clause = notify_false(variable, var_index, new_value)
            
            if not satisfiable:
                reset_propagations()
                return False, conflict_clause
            
            for (forced_lit, ant) in forced_literals:
                propagated.append((forced_lit, ant))
            
        return True, None

    def set_decision_variable(self, variable:int, variable_index:int, value:int, unit_propagation:int = True):
        """ Increments the decision level and sets the variable for this level.
            Returns if a unit propagation conflict occurs.
        """
        assert self.values[variable_index] == 0

        self.decision_level += 1
        self.values[variable_index] = value
        self.variable_levels[variable_index] = self.decision_level

        self.decision_stack.append((variable, variable_index))
        self.trails.append([])
        unit_prop_conflict = None
        conflict_clause = None
        if unit_propagation:
            unit_prop_sat, unit_prop_conflict_clause = self.unit_propagate(variable, variable_index, value)
            unit_prop_conflict = not unit_prop_sat
            conflict_clause = unit_prop_conflict_clause


        assert len(self.decision_stack) == self.decision_level
        assert len(self.trails) == self.decision_level + 1
        if unit_prop_conflict:
            assert conflict_clause != None

        return unit_prop_conflict, conflict_clause


    def search(self, nof_conflicts: int):
        assert self.decision_level == 0
        conflict_counter = 0

        def unsat_core_is_global(unsat_core):
            globally_unsat = all(self.variable_levels[self.var_index_of_lit(lit)] == 0 for lit in unsat_core)
            if globally_unsat and self.DEBUG_LEVEL >= 1:
                print(f"Unsat core consists of only level 0 variables --> unsat")
            return globally_unsat

        def make_decision(next_variable, next_variable_index, next_value):
            """Returns (is_conflict, conflict_clause, propagation_conflict: bool)."""
            propagation_conflict, propagation_clause = self.set_decision_variable(
                next_variable, next_variable_index, next_value
            )
            if propagation_conflict:
                self.bump_clause_activity(propagation_clause)
                return True, self.learnt_clauses[propagation_clause], True

            test_satisfiable, unsat_core = self.test_assignment()
            if not test_satisfiable:
                conflict_clause = literal_util.clause_from_dimacs([-1 * lit for lit in unsat_core])
                #conflict_clause = literal_util.clause_from_dimacs([var * (-1 if self.values[var_index] > 0 else 1) for var, var_index in self.decision_stack])
                assert conflict_clause != None
                return True, conflict_clause, False

            return False, None, False

        while conflict_counter < nof_conflicts or nof_conflicts == -1:
            assert len(self.decision_stack) == self.decision_level
            assert len(self.trails) == self.decision_level + 1

            # conflict, conflict_clause, propagation_conflict = ...

            if self.all_variables_set():
                test_sat, test_unsat_core = self.test_assignment()
                conflict = not test_sat
                propagation_conflict =False
                if not conflict:
                    self.model = [-var if self.values[var_index] < 0 else var
                                for var_index, var in enumerate(self.glue_variables)]
                    return True
                else:
                    conflict_clause = literal_util.clause_from_dimacs([-1 * lit for lit in test_unsat_core])
                    if unsat_core_is_global(conflict_clause):
                        return False

                    #conflict_clause = literal_util.clause_from_dimacs([var * (-1 if self.values[var_index] > 0 else 1) for var, var_index in self.decision_stack])
            else:
                next_variable_index, next_value = self.next_decision()
                next_variable = self.glue_variables[next_variable_index]
                conflict, conflict_clause, propagation_conflict = make_decision(
                    next_variable, next_variable_index, 1 if next_value else -1
                )

                # Special case where unsat_core only has level 0 variables
                if conflict and not propagation_conflict and unsat_core_is_global(conflict_clause):
                    return False

                if not conflict and len(self.learnt_clauses) - max(self.learnt_clauses._nof_locked_clauses, 0) >= self.max_learnts:
                    self.reduce_learnt_clauses()

            while conflict:
                conflict_counter += 1
                if propagation_conflict:
                    self.nof_prop_conflicts += 1
                else:
                    self.nof_test_conflicts += 1

                if self.decision_level == 0:
                    self.model = None
                    return False

                learnt_clause, btlevel = self.analyze_conflict(conflict_clause)
                self.backtrack(btlevel)

                l_conf, clause_id = self.add_learnt_clause(learnt_clause)
                if l_conf:
                    return False

                self.decay_clause_activity()
                self.decay_var_activity()

                # Increase number of learnt clauses by 10%, if we encounter 100 * 1.5^(n) conflicts
                self.learntsize_adjust_cnt -= 1
                if self.learntsize_adjust_cnt <= 0:
                    self.learntsize_adjust_confl *= self.learntsize_adjust_inc
                    self.learntsize_adjust_cnt = int(self.learntsize_adjust_confl)
                    self.max_learnts *= self.learntsize_inc

                lit = learnt_clause[0]
                var = literal_util.get_variable(lit)
                var_index = self.var_to_index[var]
                value = 1 if literal_util.is_positive(lit) else -1

                if len(learnt_clause) > 1:
                    self.enqueue(var_index, value, clause_id)
                # len == 1 case: already handled inside add_learnt_clause

                prop_sat, conflict_clause_id = self.unit_propagate(var, var_index, value)
                conflict = not prop_sat
                if conflict:
                    propagation_conflict = True
                    conflict_clause = self.learnt_clauses[conflict_clause_id]
                    assert conflict_clause is not None


            if conflict_counter >= nof_conflicts and nof_conflicts != -1:
                return None

        return None


    def enqueue(self, var_index, value, antecedent, trail = None):
        if trail == None:
            trail = self.trails[-1]
        self.values[var_index] = value
        self.variable_levels[var_index] = self.decision_level
        del self.variable_heap[var_index]
        trail.append((var_index, antecedent))
        self.learnt_clauses.set_locked(antecedent, True)

    def search_next_backtrack_level(self, randomize_decisions = False, critical = True):
        """
        Assumption: The current decision level is satisfiable!!!!
        Fast forwards to the first decision level, that results in a conflict. The decided literals will lead to a conflict.
        The caller must handle the conflict (i.e. change the last variable assignment or backtrack).

        The function will leave the solver in a state where the current assignments leads to a conflict.
        Exception: All decisions lead to a satisfiable assignment. The function will return True in this case. 
        """

        start_decision_level = self.decision_level
        possible_decisions = [(index, 1) for index, value in enumerate(self.values) if value == 0]
        if randomize_decisions:
            random.shuffle(possible_decisions)
            possible_decisions = [(index, random.choice([1, -1])) for index, _ in possible_decisions]

        assert len(possible_decisions) != 0, f"Trails length: {len(self.trails[0])} - {self.trails}"

        evaluations = [0] * len(possible_decisions)
        unsat_cores = [None] * len(possible_decisions)
        def set_up_to(level):
            assert self.decision_level == start_decision_level
            for i in range(level + 1):
                next_variable_index, next_value = possible_decisions[i]
                # Skip decision, if variable has been set by unit propagation
                #  -> the value may not be the same as possible_decisions[i]
                if self.values[next_variable_index] != 0:
                    continue
                next_variable = self.glue_variables[next_variable_index]
                unit_prop_conflict, _ = self.set_decision_variable(next_variable, next_variable_index, next_value)
                if unit_prop_conflict:
                    return True
            return False

        def reset_back_to_start():
            self.backtrack(start_decision_level)
            assert self.decision_level == start_decision_level

        start = 0
        end = len(possible_decisions)
        target = 0
        while start < end:
            target = int((start + end) / 2)

            #TODO: back to start, only to recompute everythig is extremely inefficient!
            reset_back_to_start()
            unit_prop_conflict = set_up_to(target)
            #if unit_prop_conflict:
            #    assert self.local_clauses_cause_conflict() == True
            
            satisfiable = not unit_prop_conflict
            if satisfiable:
                test_sat, unsat_core = self.test_assignment()
                satisfiable = test_sat
                unsat_cores[target] = unsat_core
            #TODO: use unit prop conflicts somehow

            evaluations[target] = 1 if satisfiable else -1
            if satisfiable:
                start = target + 1
            else:
                end = target

        if start == len(evaluations):
            if not self.all_variables_set() and self.DEBUG_LEVEL >= 2:
                print(f"target: {target}")
                print(f"evaluation: {evaluations}")
                print(f"values: {self.values}")
            assert evaluations[target] != 0
            #assert self.all_variables_set() #TODO: This function does no longer work with the heap
            assert not any(self.values[i] == 0 for i in range(len(self.values)))
            return True if evaluations[target] == 1 else False, unsat_cores[target]
        
        # Off by one problems:
        current_assignment = evaluations[target]
        assert current_assignment != 0

        if current_assignment == 1:
            #assert self.test_assignment()[0] == True and self.local_clauses_cause_conflict() == False
            assert target != len(possible_decisions) - 1, "Not all set, but at maximum level??"
            next_assignment = evaluations[target + 1]
            assert next_assignment == -1
            reset_back_to_start()
            set_up_to(target + 1)
            #assert self.test_assignment()[0] == False or self.local_clauses_cause_conflict() == True
            return False, unsat_cores[target + 1]
        
        if current_assignment == -1:
            if target == 0:
                return False, None
            #assert self.test_assignment()[0] == False or self.local_clauses_cause_conflict() == True
            prev_assignment = evaluations[target - 1]
            unsat_core = unsat_cores[target]
            assert prev_assignment != 0
            if prev_assignment == -1:
                reset_back_to_start()
                set_up_to(target - 1)
                unsat_core = unsat_cores[target - 1]
                #assert self.test_assignment()[0] == False or self.local_clauses_cause_conflict() == True
            #assert self.test_assignment()[0] == False or self.local_clauses_cause_conflict() == True
            return False, unsat_core
        
        assert True == False

    def add_learnt_clause(self, clause, clause_in_DIMACS=False):
        assert len(clause) > 0, f"Cannot learn an empty clause!"

        if clause_in_DIMACS:
            clause = literal_util.clause_from_dimacs(clause)
        
        if len(clause) == 1:
            lit = clause[0]
            var = literal_util.get_variable(lit)
            var_index = self.var_to_index[var]
            new_value = 1 if literal_util.is_positive(lit) else -1
            if self.values[var_index] != 0:
                same_value = (self.values[var_index] < 0) == (new_value < 0)
                if not same_value:
                    print(f"================")
                    print(f"  Variable: {var}, index: {var_index}")
                    print(f"  full clause: {clause}")
                    print(f"  Full values: {[(self.values[var_index], var) for var, var_index in self.decision_stack]}")
                    print(f"  Trails: {self.trails}")
                    print(f"  self value: {self.values[var_index]}")
                    print(f"  new value: {new_value}, from: {lit}")
                    print(f"================")
                    return True, None # Conflict
                return False, None # Already set to the same value

            self.values[var_index] = new_value
            self.variable_levels[var_index] = 0
            del self.variable_heap[var_index]
            if self.DEBUG_LEVEL >= 2:
                print(f"Level 0 prop: {var * (1 if literal_util.is_positive(lit) else -1)}")
            self.trails[0].append((var_index, -999))
            return False, None


        clause_id = self.learnt_clauses.add(clause, self.clause_incr)

        self.two_watched_literals.add_learnt_clause(self.twl_translation.clause_to_local(clause), clause_id, self.values)
        return False, clause_id

    def add_initial_clauses(self, num_clauses : int):
        for _ in range(num_clauses):
            clause = self.probe_for_new_clause()
            if clause == None:
                # Found a model.
                if self.DEBUG_LEVEL >= 1:
                    print(f"Found a model while probing")
                return True
            conflicting_clause, _ = self.add_learnt_clause(clause)
            if conflicting_clause:
                if self.DEBUG_LEVEL >= 1:
                    print(f"Found a conflict unit-clause during initial clause learning.")
                return False

            # All variables set during probing
            if len(self.trails[0]) == len(self.glue_variables):
                if self.local_clauses_cause_conflict():
                    return False
                return self.test_assignment()[0]
                
        self.reset_solver()
        
        return None
                            
    def probe_for_new_clause(self) -> list[int]:
        self.reset_solver(keep_global_decisions=True)

        assert self.decision_level == 0
        assert len(self.decision_stack) == 0, f"Expected exactly one decision on the stack, but got {len(self.decision_stack)}"
        assert len(self.trails) == 1, f"Expected one trail, but got {len(self.trails)}"

        all_set, unsat_core = self.search_next_backtrack_level(randomize_decisions=True)

        if all_set:
            #assert self.all_variables_set()
            self.model = [-var if self.values[var_index] < 0 else var for var_index, var in enumerate(self.glue_variables)]
            return None

        # If no unsatisfiable core is given (could be fixed), use complete assignment to learn a clause.

        new_clause = None
        # Core can be longer than 
        if unsat_core == None or len(unsat_core) > len(self.decision_stack):
            #print(f"No core)")
            new_clause = [literal_util.get_pos_lit(decision_var) if self.values[decision_var_index] < 0 else \
                literal_util.get_neg_lit(decision_var) \
                    for (decision_var, decision_var_index) in self.decision_stack]
        else:
            new_clause = [literal_util.get_pos_lit(abs(dimacs_lit)) if dimacs_lit < 0 else \
                literal_util.get_neg_lit(abs(dimacs_lit)) \
                    for dimacs_lit in unsat_core]
            #print(f"Core: {len(unsat_core)} / {len(self.decision_stack)}: {new_clause}")

        self.reset_solver(keep_global_decisions=True)
        
        return new_clause        

    def analyze_conflict(self, conflict_clause, propagation_conflict = False):
        """ Analyze a conflict and calculates a learnt clause. Return the learnt clause and a decision level to backtrack to
        """

        # conflict clause MUST be in base2 format. NOT in dimacs!
        assert self.decision_level > 0
        assert len(conflict_clause) > 0
        assert self.decision_level == len(self.trails) - 1, f"Decision Level: {self.decision_level}, but length of trails {len(self.trails)}"
        conflict_level = max(self.variable_levels[self.var_index_of_lit(lit)] for lit in conflict_clause)
        curr_level_variables = 0
        #for lit in conflict_clause:
        #    var = literal_util.get_variable(lit)
        #    var_index = self.var_to_index[var]
        #    value = self.values[var_index]
        #    assert value != 0
        #    if literal_util.is_negative(lit):
        #        assert value > 0
        #    elif literal_util.is_positive(lit):
        #        assert value < 0
        #    if self.variable_levels[var_index] == conflict_level:
        #        curr_level_variables += 1
        #assert curr_level_variables >= 1, f"Current level variables: {curr_level_variables}, expected 1. Current level: {conflict_level}"

        conflict_level_variable_indices = set([self.var_index_of_lit(lit) for lit in conflict_clause if self.variable_levels[self.var_index_of_lit(lit)] == conflict_level])
        assert conflict_level <= self.decision_level
        assert conflict_level >= 1
        assert len(conflict_level_variable_indices) >= 1
        #for var, var_index in self.decision_stack:
        #    assert self.values[var_index] != 0

        #print(f"current level: {conflict_level == self.decision_level}")

        # Calculating the UIP cut
        path_c = 0
        p = None

        seen = set()
        learnt = [-1] # Dummy. Is later replaced by the UIP
        trail = []
        trail.append((self.decision_stack[conflict_level - 1][1], None)) # decision stack is (var, var_index)
        if trail[0][0] in conflict_level_variable_indices:
            conflict_level_variable_indices.discard(trail[0][0])

        last_trail = self.trails[conflict_level]
        for i in range(len(last_trail)):
            vi, reason = last_trail[i]
            trail.append((vi, reason))
            if vi in conflict_level_variable_indices:
                conflict_level_variable_indices.discard(vi)
                if len(conflict_level_variable_indices) == 0:
                    break
        index = len(trail) - 1

        #print(f"Conflict clause: {literal_util.clause_to_dimacs(conflict_clause)} - from propagation: {propagation_conflict}")
        #print(f"Current Stack: {[var for var, _ in self.decision_stack]}")
        #print(f"Trail: {[[(self.glue_variables[var_index], antecedent if antecedent < 0 else self.learnt_clauses[antecedent]) for var_index, antecedent in self.trails[i]] for i in range(len(self.trails))]}")

        # do while loop in python: while(True) and check condition at the end
        while True:
            assert conflict_clause != None
            c = conflict_clause


            for j in range(len(c)):
                lit = c[j]
                var = literal_util.get_variable(lit)
                var_index = self.var_to_index[var]
                #print(f"  variable: {var * (-1 if literal_util.is_negative(lit) else 1)}")
                if p != None and literal_util.get_variable(p) == var:
                    #print("   -> Skip same")
                    continue

                var_level = self.variable_levels[var_index]

                assert var_level != -1
                if not var in seen and var_level > 0:
                    seen.add(var)
                    self.bump_var_activity(var_index)
                    if var_level >= conflict_level:
                        #print("   -> Skip current level")
                        path_c += 1
                    else:
                        #print(f"   -> Learnt {literal_util.get_variable(lit) * (-1 if literal_util.is_negative(lit) else 1)}, from clause {literal_util.clause_to_dimacs(c)}")
                        learnt.append(lit)
                #elif var_level <= 0:
                    #print(f"   -> Skip level {var_level}")
                #elif var in seen:
                    #print("   -> already seen")

            # while (!seen[var(trail[index--])]);
            def var_at(idx):
                var_index, _ = trail[idx]
                return self.glue_variables[var_index]
            #print(f"Seen: {seen}")
            while var_at(index) not in seen:
                index -= 1
            assert index >= 0, "backward trail scan ran off the front — pathC/seen bookkeeping is inconsistent"
            index -= 1

            p_var_index, confl_id = trail[index + 1]
            p_var = self.glue_variables[p_var_index]
            #assert p_var in seen, f"trail scan landed on unseen variable {p_var}"
            assert self.values[p_var_index] != 0
            p = literal_util.get_pos_lit(p_var) if self.values[p_var_index] > 0 else literal_util.get_neg_lit(p_var)
            seen.remove(literal_util.get_variable(p))
            path_c -= 1

            if path_c > 0:
                conflict_clause = self.learnt_clauses[confl_id]
                self.bump_clause_activity(confl_id)
                continue
            else:
                #assert p_var_index == self.decision_stack[conflict_level - 1][1] or self.variable_levels[p_var_index] == conflict_level, \
                #        "loop terminated but final literal isn't at conflict_level"
                break
                
        learnt[0] = literal_util.get_negated(p)
        assert self.variable_levels[self.var_index_of_lit(p)] == conflict_level
        #assert sum(1 if self.variable_levels[self.var_index_of_lit(l)] == conflict_level else 0 for l in learnt) == 1
        #print(f"Learnt: {literal_util.clause_to_dimacs(learnt)}")


        # Check post condition: All literals in the clause compute negative and are from earlier decision levels
        #for i in range(1, len(learnt)):
        #    lit = learnt[i]
        #    var = literal_util.get_variable(lit)
        #    var_index = self.var_to_index[var]
        #    value = self.values[var_index]
        #    assert value != 0
        #    if literal_util.is_negative(lit):
        #        assert value > 0
        #    elif literal_util.is_positive(lit):
        #        assert value < 0
        #    assert self.variable_levels[var_index] != -1
        #    assert self.variable_levels[var_index] < conflict_level


        # Calculate backtrack level: Max level of involved literals - except the UIP literal, which will be immediately propagated via unit propagation
        best_level = -1
        if len(learnt) == 1:
            best_level = 0
        else:
            max_i = 1
            best_level = self.variable_levels[self.var_index_of_lit(learnt[max_i])]
            for i in range(2, len(learnt)):
                level = self.variable_levels[self.var_index_of_lit(learnt[i])]
                if level > best_level:
                    max_i = i
                    best_level = level
        assert best_level >= 0

        return learnt, best_level

    def var_index_of_lit(self, lit):
        return self.var_to_index[literal_util.get_variable(lit)]


    # Instead of decaying every clause/variable every conflict, we increment by an exponential amount
    def decay_var_activity(self):
        self.var_incr *= 1/self.var_decay

    def decay_clause_activity(self):
        self.clause_incr *= 1 /self.clause_decay

    def bump_var_activity(self, var_index):
        self.var_activity[var_index] += self.var_incr
        if var_index in self.variable_heap:
            self.variable_heap[var_index] = -self.var_activity[var_index]
        if self.var_activity[var_index] > 1e100:
            self.var_activity = [x * 1e-100 for x in self.var_activity]
            self.var_incr *= 1e-100
            self.variable_heap.rescale(1e-100)


    def bump_clause_activity(self, clause_id):
        self.learnt_clauses.add_activity(clause_id, self.clause_incr)
        if self.learnt_clauses.get_activity(clause_id) > 1e20:
            self.learnt_clauses.rescale_activity(1e-20)
            self.clause_incr *= 1e-20

    def reduce_learnt_clauses(self):
        extra_limit = self.clause_incr / len(self.learnt_clauses)

        sorted_clause_ids = self.learnt_clauses.get_sorted_by_activity()
        half_point = int(len(sorted_clause_ids) / 2)
        for i, clause_id in enumerate(sorted_clause_ids):
            clause = self.learnt_clauses[clause_id]
            activity = self.learnt_clauses.get_activity(clause_id)
            assert len(clause) > 1
            if len(clause) == 2 or self.learnt_clauses.is_locked(clause_id) or (i < half_point and activity > extra_limit):
                continue
            del self.learnt_clauses[clause_id]
            self.two_watched_literals.delete_clause(clause_id)

    def luby_sequence(self, y: float, x: int) -> float:
        '''  Finite subsequences of the Luby-sequence:

            0: 1
            1: 1 1 2
            2: 1 1 2 1 1 2 4
            3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
        '''
        # Find the finite subsequence that contains index x,
        # and the size of that subsequence.
        size = 1
        seq = 0

        while size < x + 1:
            seq += 1
            size = 2 * size + 1

        while size - 1 != x:
            size = (size - 1) >> 1
            seq -= 1
            x = x % size

        return y ** seq




