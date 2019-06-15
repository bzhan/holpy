# Author: Bohua Zhan

"""Utility for creating new names."""

def get_new_name(n, prevs):
    """Create a name starting at n, to avoid any of the prevs."""
    if n not in prevs:
        return n

    i = 1
    while True:
        if n + str(i) not in prevs:
            return n + str(i)
        i += 1
