import time
import mtkahypar
import multiprocessing
import numpy as np

def create_context(mtk, k=2, epsilon=0.15, preset_type = mtkahypar.PresetType.DEFAULT):
    context = mtk.context_from_preset(preset_type)
    context.set_partitioning_parameters(
        k,                        # number of blocks
        epsilon,                  # imbalance parameter
        mtkahypar.Objective.CUT)  # optimize for cuts
    mtkahypar.set_seed(42)
    context.logging = False
    return context

def analyze_hypergraph(queue, num_clauses, hyperedges):
    mtk = mtkahypar.initialize(multiprocessing.cpu_count())

    context = create_context(mtk)
    hypergraph = mtk.create_hypergraph(context, num_clauses, len(hyperedges), hyperedges)
    del hyperedges  # free memory
    start = time.perf_counter()
    partitioned_hg = hypergraph.partition(context)
    print("Test")
    print(dir(partitioned_hg))
    time_partition = time.perf_counter() - start
    result = {
            "cut": partitioned_hg.cut(),
            "km1": partitioned_hg.km1(),
            "soed": partitioned_hg.soed(),
            "imbalance": partitioned_hg.imbalance(context),
            "time_partition": time_partition,
    }

    queue.put(result)

def create_partition(queue, num_clauses, hyperedges):
    mtk = mtkahypar.initialize(multiprocessing.cpu_count())

    context = create_context(mtk)
    hypergraph = mtk.create_hypergraph(context, num_clauses, len(hyperedges), hyperedges)
    start = time.perf_counter()
    partitioned_hg = hypergraph.partition(context)

    # results of print(dir(partitioned_hg))
    #['block_id', 'block_weight', 'blocks', 'connectivity', 'connectivity_set', 'cut', 'fixed_vertex_block', 'get_partition', 'imbalance', 'improve_mapping', 'improve_partition', 'is_compatible', 'is_fixed', 'is_incident_to_cut_edge', 'km1', 'num_blocks', 'num_incident_cut_edges', 'num_pins_in_block', 'soed', 'steiner_tree', 'write_partition_to_file']

    result = {
        "partition": np.array(partitioned_hg.get_partition(), dtype=np.int32)
    }
    queue.put(result)
