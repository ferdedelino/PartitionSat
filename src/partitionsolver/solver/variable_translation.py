from partitionsolver.utils import literal_util

class VariableTranslation:

    def __init__(self, variables):
        self.to_global = {}
        for i in range(len(variables)):
            self.to_global[i + 1] = variables[i]
        self.to_local = {}
        for i in range(len(variables)):
            self.to_local[variables[i]] = i + 1
        
    def variable_to_global_name(self, var: int) -> int:
        return self.to_global[var]
    
    def variable_to_local_name(self, var: int) -> int:
        return self.to_local[var]

    def lit_to_global_name(self, lit: int) -> int:
        var = literal_util.get_variable(lit)
        renamed_variable = self.to_global[var]
        if literal_util.is_negative(lit):
            return literal_util.get_neg_lit(renamed_variable)
        else:
            return literal_util.get_pos_lit(renamed_variable)
        
    def lit_to_local_name(self, lit: int) -> int:
        var = literal_util.get_variable(lit)
        renamed_variable = self.to_local[var]
        if literal_util.is_negative(lit):
            return literal_util.get_neg_lit(renamed_variable)
        else:
            return literal_util.get_pos_lit(renamed_variable)
        
    def clause_to_global(self, clause: list[int]) -> list[int]:
        return [self.lit_to_global_name(lit) for lit in clause]
    
    def clause_to_local(self, clause: list[int]) -> list[int]:
        return [self.lit_to_local_name(lit) for lit in clause]