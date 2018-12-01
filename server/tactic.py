# Author: Bohua Zhan

from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof
from logic.logic import Logic
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

def replace_id(prf, old_id, new_id):
    """Replace old_id with new_id in prevs."""
    def replace_line(item):
        return ProofItem(item.id, item.rule, args = item.args,
            prevs = [new_id if id == old_id else id for id in item.prevs], th = item.th)

    new_prf = Proof()
    new_prf.vars = prf.vars
    for item in prf.proof:
        new_prf.proof.append(replace_line(item))
    new_prf = remove_line(new_prf, old_id)

    return new_prf

def find_goal(prf, concl, upto_id):
    """Determine if the given conclusion is already proved. Search up to
    the given id.

    """
    for item in prf.get_items():
        if item.id == upto_id:
            return None
        if item.th is not None and item.th.can_prove(concl):
            return item.id

    # upto_id not found
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

    As, _ = Logic.subst_norm(th.concl, inst).strip_implies()

    num_goal = len(As) - len(prevs)
    prf = add_line_before(prf, id, num_goal)
    start = int(id[1:])
    all_ids = ["S" + str(start + i - len(prevs)) for i in range(len(prevs), len(As))]
    for goal_id, A in zip(all_ids, As[len(prevs):]):
        prf = set_line(prf, goal_id, "sorry", th = Thm(cur_item.th.assums, A))

    prf = set_line(
        prf, "S" + str(start + num_goal), "apply_theorem_for",
        args = (th_name, cur_item.th.concl), prevs = prevs + all_ids)

    # Test if the goals are already proved:
    for goal_id, A in reversed(list(zip(all_ids, As[len(prevs):]))):
        goal = Thm(cur_item.th.assums, A)
        new_id = find_goal(prf, goal, goal_id)
        if new_id is not None:
            prf = replace_id(prf, goal_id, new_id)

    return prf

def strip_all_implies(t, names):
    """Given a term of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    Return the triple ([v_1, ..., v_k], [A_1, ... A_n], C), where
    v_1, ..., v_k are new variables with the given names, and
    A_1, ..., A_n, C are the body of the input term, with bound variables
    substituted for v_1, ..., v_k.

    """
    if Term.is_all(t):
        assert len(names) > 0, "strip_all_implies: not enough names input."
        v = Var(names[0], t.arg.T)
        vars, As, C = strip_all_implies(t.arg.subst_bound(v), names[1:])
        return ([v] + vars, As, C)
    else:
        assert len(names) == 0, "strip_all_implies: too many names input."
        As, C = t.strip_implies()
        return ([], As, C)

def introduction(prf, id, names=None):
    """Introduce assumptions for a goal of the form

    !x_1 ... x_k. A_1 --> ... --> A_n --> C.

    Argument names specifies list of variable names.
    
    """
    cur_item = get_proof_item(prf, id)
    assert cur_item.rule == "sorry", "introduction: id is not a gap"

    if names is None:
        names = []

    vars, As, C = strip_all_implies(cur_item.th.concl, names)

    # Add necessary variables
    for var in vars:
        if var not in prf.vars:
            prf.vars.append(var)

    # len(As) lines for the assumptions, one line for the sorry,
    # len(vars) lines for forall_intr, len(As) lines for implies_intr,
    # one line already available.
    prf = add_line_before(prf, id, len(vars) + 2 * len(As))

    # Starting id number
    start = int(id[1:])

    # Assumptions
    for i, A in enumerate(As):
        new_id = "S" + str(start + i)
        prf = set_line(prf, new_id, "assume", args = A, th = Thm([A], A))

    # Goal
    goal_id = "S" + str(start + len(As))
    goal = Thm(list(cur_item.th.assums) + As, C)
    prf = set_line(prf, goal_id, "sorry", th = goal)

    # implies_intr invocations
    for i, A in enumerate(reversed(As)):
        prev_id = "S" + str(start + len(As) + i)
        new_id = "S" + str(start + len(As) + i + 1)
        prf = set_line(prf, new_id, "implies_intr", args = A, prevs = [prev_id])

    # forall_intr invocations
    for i, var in enumerate(reversed(vars)):
        prev_id = "S" + str(start + 2 * len(As) + i)
        new_id = "S" + str(start + 2 * len(As) + i + 1)
        prf = set_line(prf, new_id, "forall_intr", args = var, prevs = [prev_id])

    # Test if the goal is already proved
    new_id = find_goal(prf, goal, goal_id)
    if new_id is not None:
        prf = replace_id(prf, goal_id, new_id)

    return prf
