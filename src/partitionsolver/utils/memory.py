import resource


def set_memory_limit(percentage: float = 0.9):
    """Set a memory limit for the current process to a percentage of the available memory."""
    def get_memory():
        with open('/proc/meminfo', 'r') as mem:
            free_memory = 0
            for i in mem:
                sline = i.split()
                if str(sline[0]) in ('MemFree:', 'Buffers:', 'Cached:'):
                    free_memory += int(sline[1])
        return free_memory
    
    #if platform.system() != "Linux":
    #    print('Only works on linux!')
    #    return
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    bytes = (int) (get_memory() * 1024 * percentage)
    resource.setrlimit(resource.RLIMIT_AS, (bytes, hard))
    print(f"Memory limit set to {bytes / 1024**3:.1f} GB")
