import multiprocessing as mp
import time

def _solve_worker(clauses_all, queue):
    from pysat.formula import CNF
    from pysat.solvers import Cadical300
    cnf_whole = CNF(from_clauses=clauses_all)
    start = time.perf_counter()
    with Cadical300(bootstrap_with=cnf_whole) as solver:
        sat1 = solver.solve()
        elapsed_ms = 1000 * (time.perf_counter() - start)
        queue.put((sat1, elapsed_ms))

def solve_with_timeout(clauses_all, seconds):
    queue = mp.Queue()
    p = mp.Process(target=_solve_worker, args=(clauses_all, queue))
    p.start()
    p.join(seconds)

    if p.is_alive():
        p.terminate()
        p.join()
        return "unknown", -1

    return queue.get()