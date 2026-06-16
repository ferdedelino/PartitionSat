from operator import index
import random
from pysat.solvers import Kissat404
from pysat.formula import CNF
import time

from partitionsolver.solver.two_watched_literals import TwoWatchedLiterals
from partitionsolver.solver.variable_translation import VariableTranslation
from partitionsolver.utils import literal_util



class PartitionDPLL:

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
        self.two_watched_literals = TwoWatchedLiterals(self.num_gvars, [self.twl_translation.clause_to_local(clause) for clause in self.learnt_clauses], base_clauses_in_dimacs=False)

        self.solution = None

    def reset_solver(self, keep_global_decisions:bool = True, keep_learnt_clauses = True):
        self.decision_level = 0
        self.decision_stack = []

        #TODO: rewrite this

        if keep_global_decisions:
            if len(self.trails) >= 1:
                self.trails = self.trails[0:1]
                global_decision_vars = [index for var, index in self.trails[0]]
            else:
                self.trails = [[]]
                global_decision_vars = []
        else:
            self.trails = [[]]
            global_decision_vars = []

        if len(global_decision_vars) == 0:
            self.values = [0] * self.num_gvars
        else:
            self.values = [old_value if i in global_decision_vars else 0 for i, old_value in enumerate(self.values)]
        if not keep_learnt_clauses:
            self.learnt_clauses = []

        
        self.two_watched_literals = TwoWatchedLiterals(self.num_gvars, [], base_clauses_in_dimacs=False)
        for clause_id, clause in enumerate(self.learnt_clauses):
            self.two_watched_literals.add_learnt_clause(self.twl_translation.clause_to_local(clause), clause_id, self.values)


    
    def all_variables_set(self):
        return not any(x == 0 for x in self.values)

    def next_decision(self):
        for i in range(self.num_gvars):
            if self.values[i] == 0:
                return self.glue_variables[i], i, True
        return None, None, None
    
    def backtrack(self, decision_level_target:int):
        """ Resets the state of the solver to the given decision level.
            The assignment of decision_level_target are NOT changed, only assignments above that level! 
        """

        while self.decision_level > decision_level_target:
            for trail_variable, trail_variable_index in self.trails[self.decision_level]:
                self.values[trail_variable_index] = 0
            self.trails.pop()

            # Reset the decision variable of the current decision level
            variable, variable_index = self.decision_stack[self.decision_level - 1]
            self.values[variable_index] = 0
            self.decision_stack.pop()

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
            for i in range(initial_trail_length, len(trail)):
                _, var_index = trail[i]
                self.values[var_index] = 0
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
        
        forced_initial_literals, initial_satisfiable, conflict_clause = notify_false(decision_var, decision_var_index, decision_value)
        
        if not initial_satisfiable:
            #print(f"Initial Unit prop unsat: {conflict_clause}")
            return False, None
        
        propagated = [lit for (lit, _) in forced_initial_literals]
        while len(propagated) > 0:
            unit = propagated.pop()
            assert unit != 0
            variable = literal_util.get_variable(unit)
            var_index = self.var_to_index[variable]

            # variable is already set. Two options: Set to same value, or conflict
            old_value = self.values[var_index]

            if old_value != 0:
                correct = (literal_util.is_positive(unit) and old_value > 0) or \
                          (literal_util.is_negative(unit) and old_value < 0)
                if not correct:
                    #print(f"Unit prop unsat: value already set")
                    assert self.test_assignment() == False
                    reset_propagations()
                    print(f"Propagating {variable} - {variable}")
                    return False
                continue
            
            new_value = 1 if literal_util.is_positive(unit) else -1
            self.values[var_index] = new_value
            trail.append((variable, var_index))

            # Add next units implied by this assignment
            forced_literals, satisfiable, conflict_clause = notify_false(variable, var_index, new_value)
            if not satisfiable:
                reset_propagations()
                return False
            
            for (forced_lit, _) in forced_literals:
                propagated.append(forced_lit)
            
        return True

    def set_decision_variable(self, variable:int, variable_index:int, value:int, unit_propagation:int = True):
        """ Increments the decision level and sets the variable for this level.
            Returns if a unit propagation conflict occurs.
        """
        assert self.values[variable_index] == 0

        self.decision_level += 1
        self.values[variable_index] = value

        self.decision_stack.append((variable, variable_index))
        self.trails.append([])
        unit_prop_conflict = None
        if unit_propagation:
            unit_prop_conflict = self.unit_propagate(variable, variable_index, value)
            unit_prop_conflict = not unit_prop_conflict

        #if unit_prop_conflict:
        #    assert self.test_assignment() == False, f"Trails: {self.trails}"

        assert len(self.decision_stack) == self.decision_level
        assert len(self.trails) == self.decision_level + 1

        return unit_prop_conflict

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
                    sat = False
                    break
        
        return sat

    def solve(self):
        self.reset_solver()

        # Warmup
        found_model_while_probing = self.add_initial_clauses(1_000)
        print(f"Finished adding initial clauses")
        if found_model_while_probing:
            #self.model = ... is set in add_initial_clauses()
            return True
        
        self.reset_solver()

        assert self.decision_level == 0
        """ Loop invariant: A decision level is in a consistent state.
            Only outer information is backtracking! If backtracking: Next loop will decrement the decision_level, else increment 
        """
        backtracking = False
        while True:
            #print(f"decision_level: {self.decision_level}, backtracking: {backtracking} - {self.values}")
            assert len(self.decision_stack) == self.decision_level
            assert len(self.trails) == self.decision_level + 1

            if self.decision_level == 0 and backtracking:
                self.model = None
                return False

            if not backtracking:
                assert not self.all_variables_set(), "All variables are set but not backtracking - did you forget the check the assignment and return True?"
                #next_variable, next_variable_index, next_value = self.next_decision()
                #propagation_conflict = self.set_decision_variable(next_variable, next_variable_index, 1 if next_value else -1)

                #if propagation_conflict or not self.test_assignment():
                #    backtracking = True
                #    continue

                #if self.all_variables_set():
                #    self.model = [-var if self.values[var_index] < 0 else var for var_index, var in enumerate(self.glue_variables)]
                #    return True

                #backtracking = False # keep going forward
                #continue

                all_levels_sat = self.search_next_backtrack_level()
                if all_levels_sat:
                    assert self.all_variables_set()
                    assert self.test_assignment()
                    self.model = [-var if self.values[var_index] < 0 else var for var_index, var in enumerate(self.glue_variables)]
                    return True
                else:
                    #assert self.test_assignment() == False
                    backtracking = True
                continue

            # Backtracking regime
            curr_var, curr_var_index = self.decision_stack[-1]
            curr_value = self.values[curr_var_index]
            assert curr_value != 0, "Value cannot be unassigned in backtracking!"
            assert abs(curr_value) <= 2
            if abs(curr_value) == 2:
                self.backtrack(self.decision_level - 1)
                backtracking = True
                continue

            # Try other value
            new_value = -2 if curr_value > 0 else 2
            self.backtrack(self.decision_level - 1)
            propagation_conflict = self.set_decision_variable(curr_var, curr_var_index, new_value)
            if propagation_conflict or not self.test_assignment():
                self.backtrack(self.decision_level - 1)
                backtracking = True
                continue

            if self.all_variables_set():
                self.model = [-var if self.values[var_index] < 0 else var for var_index, var in enumerate(self.glue_variables)]
                return True
            
            backtracking = False



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

        assert len(possible_decisions) != 0

        evaluations = [0] * len(possible_decisions)
        def set_up_to(level):
            assert self.decision_level == start_decision_level
            for i in range(level + 1):
                next_variable_index, next_value = possible_decisions[i]
                # Skip decision, if variable has been set by unit propagation
                #  -> the value may not be the same as possible_decisions[i]
                if self.values[next_variable_index] != 0:
                    continue
                next_variable = self.glue_variables[next_variable_index]
                unit_prop_conflict = self.set_decision_variable(next_variable, next_variable_index, next_value)
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

            reset_back_to_start()
            unit_prop_conflict = set_up_to(target)
            
            satisfiable = not unit_prop_conflict and self.test_assignment()
            #print(f"Search - decision_level: {self.decision_level} - index {target - start_decision_level - 1} - set {1 if satisfiable else -1} - {self.values}")
            evaluations[target] = 1 if satisfiable else -1
            if satisfiable:
                start = target + 1
            else:
                end = target

        if start == len(evaluations):
            if not self.all_variables_set():
                print(f"target: {target}")
                print(f"evaluation: {evaluations}")
                print(f"values: {self.values}")
            assert evaluations[target] != 0
            assert self.all_variables_set()
            return True if evaluations[target] == 1 else False
        
        last_evaluation = evaluations[target]
        assert last_evaluation != 0
        if last_evaluation == 1:
            assert target != len(possible_decisions) - 1, "Not all set, but at maximum level??"
            next_assignment = evaluations[target + 1]
            assert next_assignment == -1
            reset_back_to_start()
            set_up_to(target + 1)
            #assert self.test_assignment() == False
            return False
        
        if last_evaluation == -1:
            if target == 0:
                return False
            prev_assignment = evaluations[target - 1]
            assert prev_assignment != 0
            if prev_assignment == -1:
                reset_back_to_start()
                set_up_to(target - 1)
                #assert self.test_assignment() == False
            return False
        
        assert True == False


    def add_learnt_clause(self, clause, clause_in_DIMACS=False):
        clause_id = len(self.learnt_clauses)
        if clause_in_DIMACS:
            clause = literal_util.clause_from_dimacs(clause)
        self.learnt_clauses.append(clause)
        self.two_watched_literals.add_learnt_clause(self.twl_translation.clause_to_local(clause), clause_id, self.values)

    def add_initial_clauses(self, num_clauses : int):
        learned = []
        for _ in range(num_clauses):
            clause = self.probe_for_new_clause()
            if clause == None:
                # Found a model.
                print(f"Found a model while probing")
                return True
            
            if len(clause) == 1:
                lit = clause[0]
                var = literal_util.get_variable(lit)
                self.values[self.var_to_index[var]] = 1 if literal_util.is_positive(lit) else -1
                print(f"Level 0 prop: {var * (1 if literal_util.is_positive(lit) else -1)}")
                self.trails[0].append((var, self.var_to_index[var]))
            elif len(clause) > 1:
                learned.append(clause)
        
        self.reset_solver()
        
        # TODO: Add directly, so the probing can utilize the learned clauses.
        # Needs efficient TWL implementation!
        for clause in learned:
            self.add_learnt_clause(clause)

        return False

                            
    def probe_for_new_clause(self) -> list[int]:
        self.reset_solver(keep_global_decisions=True)

        assert self.decision_level == 0
        assert len(self.decision_stack) == 0, f"Expected exactly one decision on the stack, but got {len(self.decision_stack)}"
        assert len(self.trails) == 1, f"Expected one trail, but got {len(self.trails)}"

        all_set = self.search_next_backtrack_level(randomize_decisions=True)
        if all_set:
            assert self.all_variables_set()
            self.model = [-var if self.values[var_index] < 0 else var for var_index, var in enumerate(self.glue_variables)]
            return None

        for _, i in self.decision_stack:
            assert self.values[i] != 0
        new_clause = [literal_util.get_pos_lit(decision_var) if self.values[decision_var_index] < 0 else \
                literal_util.get_neg_lit(decision_var) \
                    for (decision_var, decision_var_index) in self.decision_stack]
        #print(f"Decision Stack: {self.decision_stack}")
        #print(f"Added clause: {new_clause}")
        # todo: This might by chance find a model - adding a clause that way might prevent a model!
        
        
        assert self.test_assignment() == False, f"Level: {self.decision_level}"
        return new_clause
        