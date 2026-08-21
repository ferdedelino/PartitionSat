class ClauseAllocator:
    """
    Dict-backed clause store with stable integer ids.
    Iterating over it yields the *clauses themselves* (like a list),
    while still supporting id-based lookup/deletion (like a dict).
    """
    def __init__(self):
        self._clauses = {}       # clause_id -> clause
        self._clause_activities = {}
        self._clause_locks = {}
        self._next_id = 0
        self._nof_locked_clauses = 0

    def add(self, clause, initial_activity):
        clause_id = self._next_id
        self._next_id += 1
        self._clauses[clause_id] = clause
        self._clause_activities[clause_id] = initial_activity
        self._clause_locks[clause_id] = False
        return clause_id

    def add_activity(self, clause_id, amount):
        self._clause_activities[clause_id] += amount

    def rescale_activity(self, factor):
        for clause_id in self._clause_activities:
            self._clause_activities[clause_id] *= factor

    def get_activity(self, clause_id):
        return self._clause_activities[clause_id]

    def get_sorted_by_activity(self):
        return sorted(self._clause_activities, key=lambda cid: self._clause_activities[cid])

    def is_locked(self, clause_id):
        return self._clause_locks[clause_id]

    def set_locked(self, clause_id, locked):
        if self._clause_locks[clause_id]:
            if locked:
                return
            else:
                self._nof_locked_clauses -= 1
        else:
            if locked:
                self._nof_locked_clauses += 1
            else:
                return
        self._clause_locks[clause_id] = locked

    def get_nof_locked_clauses(self):
        return self._nof_locked_clauses

    def reset(self):
        self._clauses = {}
        self._clause_activities = {}
        self._clause_locks = {}
        self._next_id += 1
        self._nof_locked_clauses = 0

    def __getitem__(self, clause_id):
        return self._clauses[clause_id]

    def __delitem__(self, clause_id):
        del self._clauses[clause_id]
        del self._clause_activities[clause_id]
        if self._clause_locks[clause_id]:
            print(f"!! Removing locked clause. Is this intended?")
            self._nof_locked_clauses -= 1
        del self._clause_locks[clause_id]

    def __contains__(self, clause_id):
        return clause_id in self._clauses

    def __iter__(self):
        # iterate over CLAUSES, matching your old list-based usage
        return iter(self._clauses.values())

    def __len__(self):
        return len(self._clauses)

    def items(self):
        # (clause_id, clause) pairs, for when you need the id too
        return self._clauses.items()

    def keys(self):
        return self._clauses.keys()

    def values(self):
        return self._clauses.values()