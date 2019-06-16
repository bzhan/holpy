# Author: Bohua Zhan

"""Utility for creating new names."""

def get_variant_name(nm, prevs):
    """Create a name starting at nm, to avoid any of the prevs."""
    if nm not in prevs:
        return nm

    i = 1
    while True:
        if nm + str(i) not in prevs:
            return nm + str(i)
        i += 1

def get_variant_names(nms, prevs):
    """Create a list of new names starting at nms, to avoid any
    of the prevs.

    """
    if len(nms) == 0:
        return []
    nm = get_variant_name(nms[0], prevs)
    nm_rest = get_variant_names(nms[1:], prevs + [nm])
    return [nm] + nm_rest
