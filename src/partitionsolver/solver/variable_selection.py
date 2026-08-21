from random import shuffle
import random

class VariableSelector:

    def __init__(self, glue_variables:list[int]):
        self.num_gvars = len(glue_variables)
        self.glue_variables = glue_variables

        self.variable_order = [(i, random.choice([True, False])) for i in range(self.num_gvars)]

    def all_variables_set(self, values):
        return not any(x == 0 for x in values)
    
    def next_decision(self, values):
        for var_index, value in self.variable_order:
            if values[var_index] == 0:
                return self.glue_variables[var_index], var_index, value
        return None, None, None
    
    def randomize_order(self):
        shuffle(self.variable_order)
        for idx in range(len(self.variable_order)):
            i, _ = self.variable_order[idx]
            self.variable_order[idx] = (i, random.choice([True, False]))

    def sort_variables_by_activity(self, activity_scores):
        self.variable_order.sort(key=lambda x: activity_scores[x[0]][0], reverse=True)
        for i in range(self.num_gvars):
            var_index = self.variable_order[i][0]
            _, polarity = activity_scores[var_index]
            self.variable_order[i] = (var_index, polarity)