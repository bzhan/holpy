# Author: Bohua Zhan

from kernel.thm import Thm
from kernel.proof import ProofItem, Proof
from logic.matcher import Matcher

class TacticException(Exception):
    pass


def init_proof(vars, assums, concl):
    """Given a theorem statement, construct the initial partial proof.
    
    assums - assumptions of the theorem A1, ... An.
    concl - conclusion of the theorem C.
    
    Constructs:

    A1: assume A1
    ...
    An: assume An
    S1: C by sorry
    S2: An --> C by implies_intr An from S1
    ...
    S{n+1}: A1 --> ... --> An --> C by implies_intr A1 from Sn.
    
    """
    prf = Proof(*assums)
    prf.add_item("S1", "sorry", th = Thm(assums, concl))
    prf.vars = vars
    for n, assum in enumerate(reversed(assums), 2):
        prf.add_item("S" + str(n), "implies_intr", args = assum, prevs = ["S" + str(n-1)])
    return prf    

def incr_id(id, start, n):
    """Increment the given id by n, with the starting integer index given
    by start.

    """
    if id.startswith("S") and int(id[1:]) >= start:
        return "S" + str(int(id[1:]) + n)
    else:
        return id

def incr_proof_item(item, start, n):
    """Increment all ids in the given proof item."""
    return ProofItem(incr_id(item.id, start, n), item.rule, args = item.args,
        prevs = [incr_id(id, start, n) for id in item.prevs], th = item.th)

def add_line_after(prf, id):
    """Add given line after the given id."""
    # Determine the index of the new line.
    if id.startswith("S"):
        id_new = int(id[1:]) + 1
    else:
        id_new = 1

    new_prf = Proof()
    new_prf.vars = prf.vars
    for item in prf.proof:
        new_prf.proof.append(incr_proof_item(item, id_new, 1))
        if item.id == id:
            new_prf.add_item("S" + str(id_new), "")

    return new_prf

def add_line_before(prf, id, n):
    """Add given line before the given id."""
    # Determine the index of the new line.
    assert id.startswith("S"), "add_line_before"

    id_new = int(id[1:])
    new_prf = Proof()
    new_prf.vars = prf.vars
    for item in prf.proof:
        if item.id == id:
            for i in range(n):
                new_prf.add_item("S" + str(id_new + i), "")
        new_prf.proof.append(incr_proof_item(item, id_new, n))

    return new_prf

def remove_line(prf, id):
    """Remove line with the given id."""
    # Determine the index of the line to be removed.
    if id.startswith("S"):
        id_remove = int(id[1:])
    else:
        raise TacticException()

    # Decrement a single id.
    def decr_id(id):
        if id.startswith("S") and int(id[1:]) > id_remove:
            return "S" + str(int(id[1:]) - 1)
        else:
            return id

    # Decrement a proof item.
    def decr_proof_item(item):
        return ProofItem(decr_id(item.id), item.rule, args = item.args,
            prevs = [decr_id(id) for id in item.prevs], th = item.th)

    # Remove the given line. Replace all S{i} with S{i-1} whenever
    # i > id_remove.
    new_prf = Proof()
    new_prf.vars = prf.vars
    for item in prf.proof:
        if not item.id == id:
            new_prf.proof.append(decr_proof_item(item))
        
    return new_prf

def set_line(prf, id, rule, *, args = None, prevs = None, th = None):
    """Set the item with the given id to the following data."""
    new_prf = Proof()
    new_prf.vars = prf.vars
    for item in prf.proof:
        if item.id == id:
            new_prf.proof.append(ProofItem(id, rule, args = args, prevs = prevs, th = th))
        else:
            new_prf.proof.append(item)

    return new_prf

def get_proof_item(prf, id):
    """Obtain the proof item with the given id."""
    for item in prf.proof:
        if item.id == id:
            return item
    
    raise TacticException()

def apply_backward_step(prf, id, thy, th_name, *, prevs = None):
    """Apply backward step using the given theorem."""
    if prevs is None:
        prevs = []

    # Obtain the statement to be proved.
    for i, item in enumerate(prf.proof):
        if item.id == id:
            cur_item = item

    assert cur_item.rule == "sorry", "apply_backward_step: id is not a gap"

    # Instantiate the given theorem.
    th = thy.get_theorem(th_name)
    As, C = th.concl.strip_implies()
    inst = dict()
    for pat, prev in zip(As, prevs):
        item = get_proof_item(prf, prev)
        Matcher.first_order_match_incr(pat, item.th.concl, inst)
    Matcher.first_order_match_incr(C, cur_item.th.concl, inst)

    th2 = Thm.substitution(inst, th)
    As, _ = th2.concl.strip_implies()

    num_goal = len(As) - len(prevs)
    prf = add_line_before(prf, id, num_goal)
    start = int(id[1:])
    all_ids = ["S" + str(start + i - len(prevs)) for i in range(len(prevs), len(As))]
    for new_id, A in zip(all_ids, As[len(prevs):]):
        prf = set_line(prf, new_id, "sorry", th = Thm(cur_item.th.assums, A))

    prf = set_line(
        prf, "S" + str(start + num_goal), "apply_theorem_for",
        args = (th_name, cur_item.th.concl), prevs = prevs + all_ids)
    return prf

def introduction(prf, id):
    """Introduce assumptions for a goal of the form A1 --> ... --> An --> C."""
    cur_item = get_proof_item(prf, id)
    assert cur_item.rule == "sorry", "introduction: id is not a gap"

    As, C = cur_item.th.concl.strip_implies()
    prf = add_line_before(prf, id, 2 * len(As))
    start = int(id[1:])
    for i, A in enumerate(As):
        new_id = "S" + str(start + i)
        prf = set_line(prf, new_id, "assume", args = A)
    prf = set_line(prf, "S" + str(start + len(As)), "sorry", th = Thm(list(cur_item.th.assums) + As, C))
    for i, A in enumerate(reversed(As)):
        prev_id = "S" + str(start + len(As) + i)
        new_id = "S" + str(start + len(As) + i + 1)
        prf = set_line(prf, new_id, "implies_intr", args = A, prevs = [prev_id])

    return prf
