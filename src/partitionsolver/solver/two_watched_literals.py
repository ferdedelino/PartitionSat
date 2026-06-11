import numpy as np
from partitionsolver.utils import literal_util

class TwoWatchedLiterals:
    def __init__(self, num_variables, base_clauses, base_clauses_in_dimacs = True):
        self.watches = [] # What literal is each clause watching -- Maybe not numpy?
        # Assume variables are numbered 1..num_variables
        self.num_variables = num_variables

        self.base_clauses = []
        if base_clauses_in_dimacs:
            for dimacs_clause in base_clauses:
                self.base_clauses.append(literal_util.clause_from_dimacs(dimacs_clause))
        else:
            self.base_clauses = base_clauses.copy()

        for clause in self.base_clauses:
            for lit in clause:
                var = literal_util.get_variable(lit)
                if var > num_variables:
                    raise ValueError(f"Variable {var} in clause {clause} exceeds declared number of variables {num_variables}. Have you forgotten to rename the variables in the input clauses?")
        
        # What clauses are currently watching this literal
        self.watch_lists = [[] for _ in range(2 * (self.num_variables + 1))]

        # Initialize watches
        for clause_id in range(len(self.base_clauses)):
            self.watches.append([0, 0])

        # Initially watch the first two literals of each clause
        for clause_id in range(len(self.base_clauses)):
            clause = self.base_clauses[clause_id]
            self.watches[clause_id] = [clause[0], clause[1 if len(clause) > 1 else 0]]
            watched_lit1 = self.watches[clause_id][0]
            watched_lit2 = self.watches[clause_id][1]
            self.watch_lists[watched_lit1].append(clause_id)
            if len(clause) > 1:
                self.watch_lists[watched_lit2].append(clause_id)

    def notify_false(self, changed_lit:int, assignment:list[int]) -> tuple[list[tuple[int, int]], bool, int | None]:
        """
        Computes a list of literals that get implied by setting 'changed_lit' to false.
        Returns
            - List of tuples (forced_literal, antecedent)
            - bool if formula is still satisfiable
            - id of conflict clause, if formula is NOT satisfiable
        """
        assert len(assignment) == self.num_variables, f"Assignent length {len(assignment)} does not match number of variables {self.num_variables}"
        assert changed_lit > 0
        assert literal_util.get_variable(changed_lit) <= self.num_variables, f"Changed literal {literal_util.get_variable(changed_lit)} exceeds number of variables {self.num_variables}"

        forced_literals = []
        
        watch_list = self.watch_lists[changed_lit]

        # for (int ix = watchList.size() - 1; ix >= 0; ix--)
        for ix in range(len(watch_list) - 1, -1, -1):
            clause_id = watch_list[ix]

            watch = self.watches[clause_id]
            lit0 = watch[0]
            lit1 = watch[1]

            other_watch_index = 1 if changed_lit == lit0 else 0
            other_lit = lit1 if changed_lit == lit0 else lit0
            if literal_util.evaluates_positive(other_lit, assignment):
                continue

            found = False
            found_literal = -1
            for clauseLit in self.base_clauses[clause_id]:
                if clauseLit == lit0 or clauseLit == lit1:
                    continue
                if (literal_util.evaluates_negative(clauseLit, assignment)):
                    continue
                found_literal = clauseLit;
                found = True;
                break;

            if found:
                watch[1 - other_watch_index] = found_literal; # "1 -": the other watcher 1-->0, 0-->1
                watch_list.pop(ix);
                self.watch_lists[found_literal].append(clause_id);
            else:
                if literal_util.evaluates_negative(other_lit, assignment):
                    return [], False, clause_id
                else:
                    # Here we already know that otherLit is not true --> Propagate literal
                    forced_literals.append((other_lit, clause_id))
        
        return forced_literals, True, None

    def add_learnt_clause(self, clause, clause_id, assignment):
        assert len(clause) > 1, "Unit clauses should be handled separately by the solver, not added to the two watched literals data structure"
        assert clause_id == len(self.base_clauses)
        self.base_clauses.append(clause)

        # We pick any two literals to watch, that are not currently false. 
        # todo: CDCL learnt clauses should watch UIP cut and highest-decision-level remaining literal
        watched_index1 = -1
        watched_index2 = -1
        for index, lit in enumerate(clause):
            if not literal_util.evaluates_negative(lit, assignment):
                if watched_index1 == -1:
                    watched_index1 = index
                elif watched_index2 == -1:
                    watched_index2 = index
                    break
        
        # Pick variables, when all are currently false
        if watched_index1 == -1:
            watched_index1 = 0
        if watched_index2 == -1:
            watched_index2 = 1 if len(clause) > 1 else 0

        self.watches.append([clause[watched_index1], clause[watched_index2]])
        watched_lit1 = self.watches[clause_id][0]
        watched_lit2 = self.watches[clause_id][1]

        self.watch_lists[watched_lit1].append(clause_id)
        if watched_lit1 != watched_lit2:
            self.watch_lists[watched_lit2].append(clause_id)

