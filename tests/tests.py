# test_two_watched_literals.py
import pytest
from partitionsolver.solver.two_watched_literals import TwoWatchedLiterals
from partitionsolver.solver.variable_translation import VariableTranslation
from partitionsolver.solver.division_solver import DivisionDPLL
from partitionsolver.utils import literal_util

def test_notify_neg_var():
    clauses = [[1, -2], [2, 3], [-1, 2]]
    twl = TwoWatchedLiterals(3, clauses)
    result = twl.notify_false(literal_util.get_neg_lit(1), [0, 0, 0])
    expected = ([(literal_util.get_pos_lit(2), 2)], True, None)
    assert result == expected

    result = twl.notify_false(literal_util.get_neg_lit(1), [0, -1, 0])
    expected = ([], False, 2)
    assert result == expected

def test_notify_false_pos_lit():
    clauses = [[1, -2], [2, 3], [-1, 2]]
    twl = TwoWatchedLiterals(3, clauses)
    result = twl.notify_false(literal_util.get_pos_lit(1), [0, 0, 0])
    expected = ([(literal_util.get_neg_lit(2), 0)], True, None)
    assert result == expected

    result = twl.notify_false(literal_util.get_pos_lit(1), [0, 1, 0])
    expected = ([], False, 0)
    assert result == expected

def test_notify_3CNF():
    clauses = [[1, -2, 3], [2, 3, 4], [-1, 2, -4]]
    twl = TwoWatchedLiterals(4, clauses)
    result = twl.notify_false(literal_util.get_neg_lit(2), [0, 0, 0, 0])
    result = twl.notify_false(literal_util.get_pos_lit(1), [0, 1, 0, 0])
    expected = ([(literal_util.get_pos_lit(3), 0)], True, None)
    assert result == expected

    result = twl.notify_false(literal_util.get_pos_lit(3), [-1, 1, 0, 0])
    expected = ([], False, 0)
    assert result == expected

def test_unit_clause():
    clauses = [[1], [2, 3, 4]]
    twl = TwoWatchedLiterals(4, clauses)
    result = twl.notify_false(literal_util.get_pos_lit(1), [-1, 0, 0, 0])
    expected = ([], False, 0)
    assert result == expected

    result = twl.notify_false(literal_util.get_neg_lit(2), [0, 0, 0, 0])
    expected = ([], True, None)
    assert result == expected

def test_indexed_variables():
    clauses = [[3, 5], [-3, -5]]
    transl = VariableTranslation([3, 5])
    assert transl.variable_to_local_name(3) == 1
    assert transl.variable_to_local_name(5) == 2
    assert transl.variable_to_global_name(1) == 3
    assert transl.variable_to_global_name(2) == 5

    twl = TwoWatchedLiterals(2, [transl.clause_to_local(literal_util.clause_from_dimacs(clause)) for clause in clauses], False)

    false_lit = literal_util.get_pos_lit(5)
    result = twl.notify_false(transl.lit_to_local_name(false_lit), [0, 0])
    expected = ([(literal_util.get_pos_lit(1), 0)], True, None) # 1: local name for 3
    assert result == expected

    false_lit = literal_util.get_pos_lit(3)
    result = twl.notify_false(transl.lit_to_local_name(false_lit), [0, -1])
    expected = ([], False, 0)
    assert result == expected

def test_solver():
    clauses1 = [[1, -2], [2, 3], [-1, 4]]
    clauses2 = [[3, 5], [-3, 4, -5]]
    solver = DivisionDPLL(5, [3, 4], [clauses1, clauses2])
    solver.reset_solver()
    solver.decision_level = 1
    solver.add_learnt_clause([-3, 4], clause_in_DIMACS=True)
    solver.set_decision_variable(3, 0, 1)

    solver.values[1] = -1
    result = solver.unit_propagate(3, 0, 1)
    assert result == False
    
    solver.values[1] = 1
    result = solver.unit_propagate(3, 0, 1)
    assert result == True


if __name__ == "__main__":
    #test_solver()
    pytest.main([__file__, "-v"])
