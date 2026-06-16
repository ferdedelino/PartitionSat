from operator import index
import random
from pysat.solvers import Kissat404
from pysat.formula import CNF
import time

from partitionsolver.solver.two_watched_literals import TwoWatchedLiterals
from partitionsolver.solver.variable_translation import VariableTranslation
from partitionsolver.utils import literal_util


class DivisionDPLL:

    def __init__(self, num_variables:int, glue_variables:list, partial_clauses:list):
        self.num_variables = num_variables
        self.glue_variables = glue_variables
        self.partial_clauses = partial_clauses
        self.num_gvars = len(glue_variables)

        self.trails = []
        self.values = [0] * self.num_gvars

        self.var_to_index = {var: index for index, var in enumerate(glue_variables)}

        self.learnt_clauses = [] # Learnt clauses, in bitshifted variable format - NOT DIMACS
        self.twl_translation = VariableTranslation(glue_variables)
        self.tow_watched_literals = TwoWatchedLiterals(self.num_gvars, [self.twl_translation(clause) for clause in self.learnt_clauses], base_clauses_in_dimacs=False)


        self.solution = None


    def reset_solver(self, keep_global_decisions:bool = True, keep_learnt_clauses = True):
        # todo: Inconsistent naming. This does NOT reset the solver, just backtracks to decision level 0
        self.test_number = 0

        self.decision_level = 0
        self.decision_stack = []
        if keep_global_decisions:
            if len(self.trails) >= 1:
                self.trails = self.trails[0:1]
                global_decision_vars = [self.var_to_index[literal_util.get_variable(lit)] for lit in self.trails[0]]
            else:
                self.trails = [[]]
                global_decision_vars = []
        else:
            self.trails = [[]]
            global_decision_vars = []
        # values: 0: undecided | -1,-2: False | 1,2: True | abs = 1, if first choice, abs = 2, if second choice
        if len(global_decision_vars) == 0:
            self.values = [0] * self.num_gvars
        else:
            self.values = [0 if i in global_decision_vars else old_value for i, old_value in enumerate(self.values)]
        if not keep_learnt_clauses:
            pass

    def all_variables_set(self):
        return not any(x == 0 for x in self.values)

    def next_decision(self, randomize: bool = False):
        # This needs a lot of optimization!
        if not randomize:
            possible_variables = []
            for i in range(self.num_gvars):
                if self.values[i] == 0:
                    possible_variables.append(i)
                    return self.glue_variables[i], i, True
            return None, None, None

        if len(possible_variables) == 0:
            return None, None, None
        selected = possible_variables[random.randrange(0, len(possible_variables))]
        return self.glue_variables[selected], selected, random.choice([True, False]) 
    
    def backtrack(self, decision_level):
        # Reset the implied variables of the current decision level

        # todo: this looks extremely brittle
        for trail_variable, trail_variable_index in self.trails[decision_level]:
            self.values[trail_variable_index] = 0
        self.trails.pop()

        # Reset the decision variable of the current decision level
        variable, variable_index = self.decision_stack[decision_level - 1]
        self.values[variable_index] = 0
        self.decision_stack.pop()

    def unit_propagate(self, decision_var, decision_var_index, decision_value):
        """ Applies unit propagation to the given decided variable and applies all implications.
            Returns False if conflict, True otherwise.
            If conflict occurs (return False), the caller has to backtrack themselves!.
            """
        assert self.values[decision_var_index] == decision_value
        assert decision_value != 0

        trail = self.trails[-1]
        
        notify_lit = literal_util.get_pos_lit(decision_var) if decision_value < 0 else literal_util.get_neg_lit(decision_var)
        forced_initial_literals, initial_satisfiable, conflict_clause = self.tow_watched_literals.notify_false(
            self.twl_translation.lit_to_local_name(notify_lit), 
            self.values)
        
        if not initial_satisfiable:
            #print(f"Initial Unit prop unsat: {conflict_clause}")
            return False
        

        # TWL needs consecutive variable names. We need to add translations between the variable and a consecutive renaming.
        propagated_local_name = [lit for (lit, _) in forced_initial_literals]
        while len(propagated_local_name) > 0:
            unit = propagated_local_name.pop()
            assert unit != 0
            variable = literal_util.get_variable(unit)
            var_index_global = self.var_to_index[self.twl_translation.variable_to_global_name(variable)]

            # variable is already set. Two options: Set to same value, or conflict
            old_value = self.values[var_index_global]
            if old_value != 0:
                correct = (literal_util.evaluates_positive(unit, self.values) and old_value > 0) or \
                          (literal_util.evaluates_negative(unit, self.values) and old_value < 0)
                if not correct:
                    #print(f"Unit prop unsat: value already set")
                    return False
                continue
            
            # Set the unit literal
            new_value = 1 if literal_util.is_positive(unit) else -1
            self.values[var_index_global] = new_value
            trail.append((self.twl_translation.variable_to_global_name(variable), var_index_global))
            #print(f"Added trail to variable {self.twl_translation.variable_to_global_name(variable)}: {trail}")

            # Add next units implied by this assignment
            forced_literals, satisfiable, conflict_clause = self.tow_watched_literals.notify_false(
                literal_util.get_negated(unit), 
                self.values
            )
            if not satisfiable:
                #print(f"Unit prop unsat: {conflict_clause}")

                return False
            
            for (forced_lit, _) in forced_literals:
                propagated_local_name.append(forced_lit)
            
        return True

    def set_decision_variable(self, variable, variable_index, value, unit_propagation = True):
        self.values[variable_index] = value

        if len(self.decision_stack) != self.decision_level - 1:
            raise IndexError(f"Size of decisionStack ({len(self.decision_stack)}) does not correspond to decision_level {self.decision_level}")
        self.decision_stack.append((variable, variable_index))
        self.trails.append([])
        if unit_propagation:
            result = self.unit_propagate(variable, variable_index, value)
            return result
        return None

    def test_assignment(self, additional_clauses = None):
        if additional_clauses == None:
            additional_clauses = []
            for var_index, value in enumerate(self.values):
                if value == 0:
                    continue
                variable = self.glue_variables[var_index]
                if value < 0:
                    additional_clauses.append([-variable])
                else:
                    additional_clauses.append([variable])

        sat = True
        for clauses in self.partial_clauses:
            cnf = CNF(from_clauses=clauses)
            cnf.extend(additional_clauses)
            cnf.nv = self.num_variables
            with Kissat404(bootstrap_with=cnf) as solver:
                if not solver.solve():
                    #print(f"Found conflict at level {self.decision_level} - {self.values}")
                    sat = False
                    break
        
        return sat

    def solve(self):
        self.reset_solver()
        self.decision_level = 1 # 0 means universal level

        start = time.perf_counter()
        # Only learn clauses on the initial solve
        #self.add_initial_clauses(1_000)
        print(f"Added initial clauses in {1000 * (time.perf_counter() - start):.2f}ms")

        backtracking = False
        possible_model = [1, -2, 3, 9, 10, -11, -12, 14, -15, 16, -17, -19, 20, -21, 22, -24, -26, 27, 28, 30, 34, 36, -37, -39, -40, 41, 43, -44, -45, 46, -47, -48, 49]
        possible_decisions = [abs(d) for d in possible_model]
        while True:
            assert len(self.decision_stack) == self.decision_level - 1, f"Decision Level: {self.decision_level} - stack length: {len(self.decision_stack)}"
            assert len(self.trails) == self.decision_level, f"Decision Level: {self.decision_level} - trails length: {len(self.trails)}"
            #if backtracking:
            #    print(f"Backtracking from: {self.decision_level}")
            #    return
            #if backtracking:
            #    print(f"Backtrackig to: {self.decision_level}")
            #print(f"Testing decision Level: {self.decision_level}, backtracking: {backtracking}")
            
            critical = False
            if self.values == [1, -2, 1, 1, 1, -2, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, -2, 1, 1, 1, 1, 1, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]:
                critical = True
                print(f"TEST!!!!!!!! {self.values}")
            print(f"Next iteration: {self.decision_level} - {self.values}")
            # Backtrack to level 0: level 1 is unsatisfiable
            if self.decision_level <= 0:
                self.solution = None
                return False
            
            if self.all_variables_set():
                # todo: Really test this. I am NOT convinced any longer this works
                #satisfiable = not backtracking or self.test_assignment()
                satisfiable = self.test_assignment()
                if satisfiable:
                    self.solution = self.values.copy()
                    return True
                else:
                    if critical:
                        print("111111111")
                    backtracking = True
            
            next_variable, next_variable_index, next_value = None, None, None
            if backtracking:
                print(f" ===== {self.decision_level} - {self.decision_stack}")
                decided_variable, decided_variable_index = self.decision_stack[self.decision_level - 2]
                decided_value = self.values[decided_variable_index]

                # Abs of 2: both options have been tried, need to backtrack again
                if abs(decided_value) == 2:
                    self.backtrack(self.decision_level)
                    self.decision_level -= 1
                    continue
                if decided_value == 0:
                    raise Exception("Backtracking to a decision level with an undecided variable")
                
                # Reset the first decision, then change to the next value
                self.backtrack(self.decision_level - 1)
                self.decision_level -= 1
                next_variable = decided_variable
                next_variable_index = decided_variable_index

                # Change false <--> true
                next_value = -2 if decided_value == 1 else 2

                unit_prop_satisfiable = self.set_decision_variable(next_variable, next_variable_index, next_value)
                self.decision_level += 1
                #if not unit_prop_satisfiable:
                #    print("============= Unit prop unsat!")
                satisfiable = unit_prop_satisfiable and self.test_assignment()
                if not satisfiable:
                    if critical:
                        print("222222222")
                    backtracking = True
                    # decisionlevel stays the same - gets decremented 10 in the start of the loop
                else:
                    backtracking = False
                    self.decision_level += 1
                
                continue
            
            # todo: compute trails
            all_iterations_are_sat = self.search_next_backtrack_level(critical=critical)
            if all_iterations_are_sat:
                assert self.all_variables_set()
                self.solution = self.values.copy()
                return True
            
            if critical:
                print("3333333")
            backtracking = True

    def search_next_backtrack_level_old(self, randomize_decisions = False, critical = True):
        if critical:
            print([-var if self.values[i] < 0 else var for var, i in self.decision_stack])
        base_decision_level = self.decision_level
        possible_decisions = [(index, 1) for index, value in enumerate(self.values) if value == 0]
        evaluations = [0] * len(possible_decisions)
        if critical:
            print(f"Possible decision: {[(self.glue_variables[i], v) for i, v in possible_decisions]}")
            print(f"Decision Level: {self.decision_level}")
        # todo: order possible_decisions + add True/False as base values
        if randomize_decisions:
            random.shuffle(possible_decisions)
            possible_decisions = [(index, random.choice([1, -1])) for index, _ in possible_decisions]
        
        def set_up_to(level):
            while self.decision_level < level:
                next_variable_index, next_value = possible_decisions[self.decision_level - base_decision_level]
                next_variable = self.glue_variables[next_variable_index]
                unit_prop_sat = self.set_decision_variable(next_variable, next_variable_index, next_value)
                self.decision_level += 1
                if not unit_prop_sat:
                    return True
            return False

        def reset_back_to(target):
            while self.decision_level > target:
                self.decision_level -= 1
                self.backtrack(self.decision_level)

        start = 0
        end = len(possible_decisions)

        target_level = 0
        last_iteration_was_sat = False
        all_iterations_are_sat = True
        num_iterations = 0
        while True:
            target_level = int((start + end) / 2)
            if start >= end:
                #if all_iterations_are_sat:
                #    print(f"Stop search after {num_iterations} iterations, gvars: {self.num_gvars}, start: {start}")
                #    print(f"set variables: {len([v for v in self.values if v != 0])}, all set: {self.all_variables_set()}")
                break
            num_iterations += 1
            unit_prop_conflict = False
            if self.decision_level > base_decision_level + target_level:
                reset_back_to(base_decision_level + target_level)
            if self.decision_level < base_decision_level + target_level:
                unit_prop_conflict = set_up_to(base_decision_level + target_level)
                if unit_prop_conflict:
                    end = self.decision_level - base_decision_level
            
            satisfiable = not unit_prop_conflict and self.test_assignment()
            evaluations[target_level] = 1 if satisfiable else -1 
            if critical:
                print(f"Testing level {base_decision_level} + {target_level}, got: {satisfiable}")
            last_iteration_was_sat = satisfiable
            if satisfiable:
                start = target_level + 1
            else:
                end = target_level
                all_iterations_are_sat = False
        
        # All iterations were satisfiable - found a model
        if eval[-1] == 1:
            return True

        # Make sure the current decision level is unsatisfiable
        if last_iteration_was_sat:
            if critical:
                print(f"last_iteration_was_sat - Set up to {self.decision_level + 1}")
            all_iterations_are_sat = False # We do not know this any longer # todo: this may cause an additional computation. May improve
            set_up_to(self.decision_level + 1)
        
        self.decision_level -= 1 # backtracking expects the decision_level to be the conflict level
        if critical:
            print(f"Decision Level: {self.decision_level}")

        return all_iterations_are_sat


    def search_next_backtrack_level(self, randomize_decisions = False, critical = True):
        """
        Assumption: The current decision level is satisfiable!!!!
        Fast forwards to the first decision level, that results in a conflict. The decided literals will lead to a conflict.
        The caller must handle the conflict (i.e. change the last variable assignment or backtrack).

        Exception: All decisions lead to a satisfiable assignment. The function will return True in this case. 
        """

        print(f"Start at {self.decision_level} with values {self.values}")
        start_decision_level = self.decision_level
        possible_decisions = [(index, 1) for index, value in enumerate(self.values) if value == 0]

        assert len(possible_decisions) != 0

        evaluations = [0] * len(possible_decisions)
        def set_up_to(level):
            while self.decision_level < level:
                next_variable_index, next_value = possible_decisions[self.decision_level - start_decision_level]
                next_variable = self.glue_variables[next_variable_index]
                unit_prop_sat = self.set_decision_variable(next_variable, next_variable_index, next_value)
                self.decision_level += 1
                if not unit_prop_sat:
                    assert True == False
                    return True
            return False

        def reset_back_to(target):
            while self.decision_level > target:
                self.decision_level -= 1
                self.backtrack(self.decision_level)

        start = self.decision_level + 1
        end = self.decision_level + len(possible_decisions)
        target = 0

        while start < end:
            target = int((start + end) / 2)

            unit_prop_conflict = False
            if target > self.decision_level:
                unit_prop_conflict = set_up_to(target)
            else:
                reset_back_to(target)
            
            satisfiable = not unit_prop_conflict and self.test_assignment()
            print(f"Search - decision_level: {self.decision_level} - index {target - start_decision_level - 1} - set {1 if satisfiable else -1} - {self.values}")
            evaluations[target - start_decision_level - 1] = 1 if satisfiable else -1
            if satisfiable:
                start = self.decision_level + 1
            else:
                end = self.decision_level

        assert self.decision_level > start_decision_level, f"target: {target} - {evaluations}"
        assert target == self.decision_level, f"target: {target} - {evaluations}"

        target_evaluation = evaluations[self.decision_level - start_decision_level - 1]
        assert target_evaluation != 0, f"target: {target} - {evaluations}"

        if len(possible_decisions) == 1:
            assert self.decision_level == start_decision_level + 1, f"target: {target} - {evaluations}"
            if evaluations[self.decision_level - start_decision_level - 1] == 1:
                return True
            else:
                assert self.test_assignment() == False
                return False

        # currently negative ->
        if target_evaluation == -1:
            previous_evaluation = evaluations[self.decision_level - start_decision_level - 1 - 1]
            assert previous_evaluation != 0, f"target: {target} - {evaluations}"
            if previous_evaluation == - 1:
                old = self.decision_level
                print("Move 1 down")
                reset_back_to(self.decision_level - 1)
                assert self.decision_level == old - 1
                self.decision_level -= 1


        if target_evaluation == 1:
            next_evaluation = evaluations[self.decision_level - start_decision_level - 1 + 1]
            assert next_evaluation == -1, f"target: {target} - {evaluations}"
            print(f"MOve 1 up - {self.values}")
            old = self.decision_level
            set_up_to(self.decision_level + 1)
            print(f"MOve 1 after - {self.values}")
            assert self.decision_level == old + 1

        assert self.test_assignment() == False, f"target: {target}, dec_level: {self.decision_level} - {evaluations} - values: {self.values}"
        print(f"Finished with decision_level {self.decision_level} - {self.values}")
        return False


    def add_learnt_clause(self, clause, clause_in_DIMACS=False):
        clause_id = len(self.learnt_clauses)
        if clause_in_DIMACS:
            clause = literal_util.clause_from_dimacs(clause)
        self.learnt_clauses.append(clause)
        self.tow_watched_literals.add_learnt_clause(self.twl_translation.clause_to_local(clause), clause_id, self.values)

    def add_initial_clauses(self, num_clauses : int):
        for _ in range(num_clauses):
            clause = self.probe_for_new_clause()
            if len(clause) == 1:
                lit = clause[0]
                var = literal_util.get_variable(lit)
                self.values[self.var_to_index[var]] = 1 if literal_util.is_positive(lit) else -1
                self.trails[0].append(lit)
                print("Added level 0 decision!!!!")
            elif len(clause) > 1:
                self.add_learnt_clause(clause)
        self.reset_solver()
        self.decision_level = 1

                            
    def probe_for_new_clause(self) -> list[int]:
        self.reset_solver(keep_global_decisions=True)
        self.decision_level = 1

        assert self.decision_level == 1
        assert len(self.decision_stack) == 0, f"Expected exactly one decision on the stack, but got {len(self.decision_stack)}"
        assert len(self.trails) == 1, f"Expected one trail, but got {len(self.trails)}"
        assert self.values == [0] * self.num_gvars

        self.search_next_backtrack_level(randomize_decisions=True)
        # for the extrem improbable chance that all_iterations_are_sat is true: return model?
        return [literal_util.get_pos_lit(decision_var) if self.values[decision_var_index] < 0 else \
                literal_util.get_neg_lit(decision_var) \
                    for (decision_var, decision_var_index) in self.decision_stack]

