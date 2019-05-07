# Author: Bohua Zhan

from kernel.term import Term, Var
from kernel.proof import id_force_tuple, Proof
from logic.proofterm import ProofTermAtom
from syntax import parser
from server import tactic

global_methods = dict()

class Method:
    """Methods represent potential actions on the state."""
    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, args, prevs):
        pass

class cases_method(Method):
    """Case analysis."""
    def __init__(self):
        self.sig = {'case': str}

    def search(self, state, id, prevs):
        return True

    def apply(self, state, id, data, prevs):
        A = parser.parse_term(state.thy, state.get_ctxt(id), data['case'])
        state.apply_tactic(id, tactic.cases(), args=A)

class apply_prev_method(Method):
    """Apply previous fact."""
    def __init__(self):
        self.sig = {}

    def search(self, state, id, prevs):
        return len(prevs) == 1

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.apply_prev(), prevs=prevs)

class rewrite_goal_with_prev_method(Method):
    """Rewrite using previous fact."""
    def __init__(self):
        self.sig = {}

    def search(self, state, id, prevs):
        return len(prevs) == 1

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rewrite_goal_with_prev(), prevs=prevs)

class rewrite_goal(Method):
    """Rewrite using a theorem."""
    def __init__(self):
        self.sig = {'theorem': str}

    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rewrite(), args=data['theorem'])

class apply_forward_step(Method):
    """Apply theorem in the forward direction."""
    def __init__(self):
        self.sig = {'theorem': str}

    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, data, prevs):
        assert prevs, "apply_forward_step: prevs is not empty"
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_theorem', args=data['theorem'], prevs=prevs)

class apply_backward_step(Method):
    """Apply theorem in the backward direction."""
    def __init__(self):
        self.sig = {'theorem': str}

    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rule(), args=data['theorem'], prevs=prevs)

class introduction(Method):
    """Introducing variables and assumptions."""
    def __init__(self):
        self.sig = {}

    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"

        prop = cur_item.th.prop
        assert prop.is_implies() or prop.is_all(), "introduction"

        cur_item.rule = "subproof"
        cur_item.subproof = Proof()

        intros_tac = tactic.intros()
        pt = intros_tac.get_proof_term(state.thy, cur_item.th, args=data['names'])
        cur_item.subproof = pt.export(prefix=id)
        state.check_proof(compute_only=True)

        # Test if the goal is already proved
        for item in cur_item.subproof.items:
            new_id = state.find_goal(state.get_proof_item(item.id).th, item.id)
            if new_id is not None:
                state.replace_id(item.id, new_id)

class forall_elim(Method):
    """Elimination of forall statement."""
    def __init__(self):
        self.sig = {'s': str}

    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, data, prevs):
        t = parser.parse_term(state.thy, state.get_ctxt(id), data['s'])
        state.add_line_before(id, 1)
        state.set_line(id, 'forall_elim', args=t, prevs=prevs)

class induction(Method):
    """Apply induction."""
    def __init__(self):
        self.sig = {'theorem': str, 'var': str}

    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, data, prevs):
        # Find variable
        ctxt = state.get_ctxt(id)
        assert data['var'] in ctxt, "induction: cannot find variable."
        var = Var(data['var'], ctxt[data['var']])

        state.apply_tactic(id, tactic.var_induct(), args=(data['theorem'], var))


def apply_method(state, data):
    method_name = data['method_name']
    assert method_name in global_methods, \
        "apply_method: method " + method_name + " not found"

    method = global_methods[method_name]
    goal_id = id_force_tuple(data['goal_id'])
    fact_ids = [id_force_tuple(fact_id) for fact_id in data['fact_ids']] if data['fact_ids'] else []
    return method.apply(state, goal_id, data, fact_ids)


global_methods.update({
    "cases": cases_method(),
    "apply_prev": apply_prev_method(),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_method(),
    "rewrite_goal": rewrite_goal(),
    "apply_forward_step": apply_forward_step(),
    "apply_backward_step": apply_backward_step(),
    "introduction": introduction(),
    "forall_elim": forall_elim(),
    "induction": induction(),
})
