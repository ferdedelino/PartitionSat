from abc import ABC, abstractmethod
from pysat.formula import CNF


class FormulaSplits(ABC):

    @abstractmethod
    def split_formula(self, clauses: list[list[int]], num_variables: int, num_clauses: int) -> tuple[list[CNF], list[int]]:
        """Takes in a set of clauses, the number of variables and the number of clauses.
           Reurns a partition of clauses and a list of shared variables.
        """
        pass


