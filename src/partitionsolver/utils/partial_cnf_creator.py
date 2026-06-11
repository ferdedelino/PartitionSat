from partitionsolver.utils import file_reader
from multiprocessing import Process, Queue
import partitionsolver.utils.hypergraph_worker as hypergraph_worker


def create_split_formula(file_location:str, display_progress:bool = False):
    num_vars, num_clauses, hyperedges = file_reader.hypergraph_from_cnf_xz(file_location, display_progress)
    queue = Queue()
    p = Process(target=hypergraph_worker.analyze_hypergraph, args=(queue, num_clauses, hyperedges))
    p.start()
    p.join()
    error = True
    if p.exitcode != 0:
        if display_progress:
            print(f"Partitioning failed with exit code {p.exitcode} ({file_location})")
    
    result = queue.get()
    hyperedges = result["hyperedges"]
    
        
    