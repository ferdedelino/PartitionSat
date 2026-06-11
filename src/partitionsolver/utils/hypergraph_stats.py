import time
import os
import json
from multiprocessing import Process, Queue
from partitionsolver.utils import file_reader
import partitionsolver.utils.hypergraph_worker as hypergraph_worker
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[3]
stats_file = PROJECT_ROOT / "output" / "stats.json"
stats_file_old = PROJECT_ROOT / "output" / "stats_old.json"
stats = None


def read_or_create_hypergraph_stats(directory, max: int=10, create_if_not_exists: bool=True, display_progress: bool=False, read_fresh:bool = False):
    """Reads the stats file if it exists, otherwise creates it by processing the .cnf.xz files in the given directory."""
    global stats
    if stats is None:
        try:
            with open(stats_file) as f:
                stats = json.load(f)
        except FileNotFoundError:
            stats = {}

    processed_amount = 0
    for entry in os.scandir(directory):
        if not entry.is_file():
            continue
        max -= 1
        if max < 0:
            break        
        processed_amount += 1
        if read_fresh:
            if stats.get(entry.name) is not None or not create_if_not_exists:
                continue
        
        if display_progress:
            print(f"Processing {entry.name[0:5]} - number ({processed_amount}):")
        start = time.perf_counter()

        num_vars, num_clauses, hyperedges = file_reader.hypergraph_from_cnf_xz(entry.path, display_progress, remove_empty_hyperedges=True)
        num_hyperedges = len(hyperedges)

        time_read = time.perf_counter() - start
        start = time.perf_counter()

        # Do the partitioning in a seperate process to catch OOMs
        queue = Queue()
        p = Process(target=hypergraph_worker.analyze_hypergraph, args=(queue, num_clauses, hyperedges))
        p.start()
        p.join()
        error = True
        if p.exitcode == 0:
            error = False
            result = queue.get()
            if display_progress:
                print(f"Partitioning completed)")
        else:
            if display_progress:
                print(f"Partitioning failed with exit code {p.exitcode} ({entry.name})")
        
        stats[entry.name] = {
                "num_vars": num_vars,
                "num_clauses": num_clauses,
                "hyperedges": num_hyperedges,
                "partition_error": error,
                "cut": None if error else result["cut"],
                "km1": None if error else result["km1"],
                "soed": None if error else result["soed"],
                "imbalance": None if error else result["imbalance"],
                "time_read": time_read,
                "time_partition": None if error else result["time_partition"]
        }
    return stats

def load_stats_file():
    global stats
    if stats is None:
        try:
            with open(stats_file) as f:
                stats = json.load(f)
        except FileNotFoundError:
            print(f"NOT FOUND!!!! {stats_file}")
            stats = {}
    return stats

def save_stats():
    global stats
    if stats is None:
        return
    
    old_stats = {}
    try:
        with open(stats_file_old) as f:
            old_stats = json.load(f)
    except FileNotFoundError:
        old_stats = {}

    with open(stats_file_old, "w") as f:
        json.dump(old_stats, f, indent=2)
    with open(stats_file, "w") as f:
        json.dump(stats, f, indent=2)