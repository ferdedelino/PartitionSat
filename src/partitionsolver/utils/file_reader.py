import mtkahypar
import time
import lzma
from os import DirEntry
import numpy as np
import psutil


def hypergraph_from_cnf_xz(file_location:str, display_progress:bool = False, remove_empty_hyperedges:bool = False):
    """Reads a .cnf or .cnf.xz file and creates a hypergraph representation of it."""
    # I know, this shit can be done MUCH faster, but Python says No.

    start = time.perf_counter()
    opener = lzma.open if file_location.endswith(".xz") else open
    
    # First pass: count sizes
    num_vars = -1
    num_clauses = -1

    with opener(file_location, 'rt') as f:
        hyperedge_sizes = None
        for line in f:
            if line.startswith('%'):
                break
            if line.startswith('c') or line.strip() == "":
                continue
            if line.startswith('p'):
                args = line.split()
                num_vars = int(args[2])
                num_clauses = int(args[3])
                hyperedge_sizes = np.zeros(num_vars, dtype=int)
                continue
            if num_vars == -1:
                raise ValueError("Invalid CNF file: missing problem line")
            literals = line.split()
            for lit in literals:
                if int(lit) == 0:
                    continue
                var = abs(int(lit)) - 1
                hyperedge_sizes[var] += 1

    if display_progress:
        print(f"Sizes counted in {time.perf_counter() - start:.2f}s")
        start = time.perf_counter()

    # Allocate
    hyperedges = np.empty(num_vars, dtype=object)
    hyperedge_indices = np.zeros(num_vars, dtype=int)
    for i in range(num_vars):
        hyperedges[i] = np.zeros(hyperedge_sizes[i], dtype=int)

    if display_progress:
        print(f"Memory allocated in {time.perf_counter() - start:.2f}s")
        print(f"Memory used: {psutil.virtual_memory().used / 1024**3:.2f} GB")
        start = time.perf_counter()

    # Second pass: fill
    with opener(file_location, 'rt') as f:
        clause_number = 0
        for line in f:
            if line.startswith('%'):
                break
            if line.startswith('c') or line.startswith('p'):
                continue
            for lit in line.split():
                val = int(lit)
                if val == 0:
                    continue
                var = abs(val) - 1
                hyperedges[var][hyperedge_indices[var]] = clause_number
                hyperedge_indices[var] += 1
                    
            clause_number += 1

    if display_progress:
        print(f"Edges filled in {time.perf_counter() - start:.2f}s")
        print(f"Memory used: {psutil.virtual_memory().used / 1024**3:.2f} GB")
        start = time.perf_counter()

    del hyperedge_indices  # free memory
 
    if not remove_empty_hyperedges:
        del hyperedge_sizes  # free memory
        return num_vars, num_clauses, hyperedges

    mask = hyperedge_sizes > 0
    del hyperedge_sizes  # free memory
    cleaned_hyperedges = hyperedges[mask]
    del hyperedges  # free memory

    if display_progress:
        print(f"Hyperedges cleaned in {time.perf_counter() - start:.2f}s")
    
    return num_vars, num_clauses, cleaned_hyperedges


def read_cnf(file_location:str):
    """Reads a .cnf or .cnf.xz file and creates an arry of clauses."""

    start = time.perf_counter()
    opener = lzma.open if file_location.endswith(".xz") else open

    
    # First pass: count sizes
    num_vars = -1
    num_clauses = -1
    clauses = None

    with opener(file_location, 'rt') as f:
        clause_id = 0
        for line in f:
            if line.startswith('%'):
                break
            if line.startswith('c') or line.strip() == "":
                continue
            if line.startswith('p'):
                args = line.split()
                num_vars = int(args[2])
                num_clauses = int(args[3])
                clauses = np.zeros(num_clauses, dtype=object)
                continue
            if num_vars == -1:
                raise ValueError("Invalid CNF file: missing problem line")
            literals = line.split()
            length = len(literals) - 1
            clause = np.empty(length, dtype=int)
            clause_index = 0
            for litstring in literals:
                lit = int(litstring)
                if int(lit) == 0:
                    continue
                clause[clause_index] = lit
                clause_index += 1
            clauses[clause_id] = clause
            clause_id += 1
    
    return num_vars, num_clauses, clauses
