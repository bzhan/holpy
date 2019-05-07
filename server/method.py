# Author: Bohua Zhan

from kernel.term import Term
from logic.proofterm import ProofTermAtom
from syntax import parser
from server.server import id_force_tuple
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
        self.sig = {'case': Term}

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


def apply_method(state, data):
    method_name = data['method_name']
    assert method_name in global_methods, \
        "apply_method: method " + method_name + " not found"

    method = global_methods[method_name]
    return method.apply(state, data['goal_id'], data, data['fact_ids'])


global_methods.update({
    "cases": cases_method(),
    "apply_prev": apply_prev_method(),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_method(),
})
