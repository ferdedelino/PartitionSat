def get_variable(literal: int) -> int:
    return literal >> 1

def get_pos_lit(var: int) -> int:
    return var << 1

def get_neg_lit(var: int) -> int:
    return (var << 1) + 1

def is_positive(literal: int) -> bool:
    return (literal & 1) == 0

def is_negative(literal: int) -> bool:
    return (literal & 1) == 1

def get_negated(literal: int) -> int:
    return literal ^ 1

def evaluates_positive(lit: int, assignment: list[int]) -> bool:
    if is_negative(lit):
        return assignment[get_variable(lit) - 1] < 0
    return assignment[get_variable(lit) - 1] > 0

def evaluates_negative(lit: int, assignment: list[int]) -> bool:
    if is_negative(lit):
        return assignment[get_variable(lit) - 1] > 0
    return assignment[get_variable(lit) - 1] < 0

def evaluate(other_watched_lit: int, assignment: list[int]) -> int:
    if evaluates_positive(other_watched_lit, assignment):
        return 1
    if evaluates_negative(other_watched_lit, assignment):
        return -1
    return 0

def clause_from_dimacs(clause: list[int]) -> list[int]:
    new_clasue = []
    for dimacs_literal in clause:
        if dimacs_literal < 0:
            new_clasue.append(get_neg_lit(abs(dimacs_literal)))
        else:
            new_clasue.append(get_pos_lit(abs(dimacs_literal)))
    return new_clasue

def clause_to_dimacs(clause: list[int]) -> list[int]:
    return [get_variable(lit) * (-1 if is_negative(lit) else 1) for lit in clause]