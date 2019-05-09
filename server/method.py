# Author: Bohua Zhan

from kernel import term
from kernel.term import Term, Var
from kernel.proof import id_force_tuple, Proof
from kernel.theory import Method, global_methods
from logic.conv import top_conv, rewr_conv, beta_conv, then_conv
from logic.proofterm import ProofTermAtom
from logic import matcher
from logic import logic
from syntax import parser
from server import tactic


class cases_method(Method):
    """Case analysis."""
    def __init__(self):
        self.sig = ['case']

    def search(self, state, id, prevs):
        return []

    def apply(self, state, id, data, prevs):
        A = parser.parse_term(state.thy, state.get_ctxt(id), data['case'])
        state.apply_tactic(id, tactic.cases(), args=A)

class apply_prev_method(Method):
    """Apply previous fact."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            cur_th = state.get_proof_item(id).th
            if prev_th.prop.is_implies() and prev_th.prop.arg == cur_th.prop:
                return [{"_goal": prev_th.assums}]
            else:
                return []
        else:
            return []

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.apply_prev(), prevs=prevs)

class rewrite_goal_with_prev_method(Method):
    """Rewrite using previous fact."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        if len(prevs) != 1:
            return []
        
        prev_th = state.get_proof_item(prevs[0]).th
        cur_th = state.get_proof_item(id).th

        if not prev_th.prop.is_equals():
            return []

        pt = ProofTermAtom(prevs[0], prev_th)
        cv = then_conv(top_conv(rewr_conv(pt, match_vars=False)),
                       top_conv(beta_conv()))
        eq_th = cv.eval(state.thy, cur_th.prop)
        new_goal = eq_th.prop.rhs

        new_As = list(set(eq_th.hyps) - set(cur_th.hyps))
        if cur_th.prop != new_goal:
            if Term.is_equals(new_goal) and new_goal.lhs == new_goal.rhs:
                return [{"_goal": new_As}]
            else:
                return [{"_goal": [new_goal] + new_As}]
        else:
            return []

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rewrite_goal_with_prev(), prevs=prevs)

class rewrite_goal(Method):
    """Rewrite using a theorem."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs):
        cur_th = state.get_proof_item(id).th
        if cur_th.prop.is_all():
            return []

        thy = state.thy
        results = []
        for th_name, th in thy.get_data("theorems").items():
            if 'hint_rewrite' not in thy.get_attributes(th_name):
                continue

            cv = top_conv(rewr_conv(th_name))
            th = cv.eval(thy, cur_th.prop)
            new_goal = th.prop.rhs
            new_As = list(th.hyps)
            if cur_th.prop != new_goal:
                if Term.is_equals(new_goal) and new_goal.lhs == new_goal.rhs:
                    results.append({"theorem": th_name, "_goal": new_As})
                else:
                    results.append({"theorem": th_name, "_goal": [new_goal] + new_As})

        return sorted(results, key = lambda d: d['theorem'])

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rewrite(), args=data['theorem'])

class apply_forward_step(Method):
    """Apply theorem in the forward direction."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        thy = state.thy
        if len(prevs) == 0:
            return []

        results = []
        for name, th in thy.get_data("theorems").items():
            if 'hint_forward' not in thy.get_attributes(name):
                continue

            instsp = (dict(), dict())
            As, C = th.prop.strip_implies()

            if len(prevs) != len(As):
                continue

            if set(term.get_vars(As)) != set(term.get_vars(As + [C])):
                continue

            if not term.get_consts(As):
                continue

            try:
                for pat, prev in zip(As, prev_ths):
                    matcher.first_order_match_incr(pat, prev.concl, instsp)
            except matcher.MatchException:
                continue

            # All matches succeed
            t = logic.subst_norm(th.prop, instsp)
            _, new_fact = t.strip_implies()
            results.append({"theorem": name, "_fact": [new_fact]})
        return sorted(results, key = lambda d: d['theorem'])

    def apply(self, state, id, data, prevs):
        assert prevs, "apply_forward_step: prevs is not empty"
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_theorem', args=data['theorem'], prevs=prevs)

class apply_backward_step(Method):
    """Apply theorem in the backward direction."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs):
        goal_th = state.get_proof_item(id).th
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        thy = state.thy

        results = []
        for name, th in thy.get_data("theorems").items():
            if 'hint_backward' not in thy.get_attributes(name):
                continue

            instsp = (dict(), dict())
            As, C = th.assums, th.concl
            # Only process those theorems where C and the matched As
            # contain all of the variables.
            if set(term.get_vars(As[:len(prevs)] + [C])) != set(term.get_vars(As + [C])):
                continue

            # When there is no assumptions to match, only process those
            # theorems where C contains at least a constant (skip falseE,
            # induction theorems, etc).
            if len(prevs) == 0 and term.get_consts(C) == []:
                continue

            try:
                if matcher.is_pattern(C, []):
                    matcher.first_order_match_incr(C, goal_th.prop, instsp)
                    for pat, prev in zip(As, prev_ths):
                        matcher.first_order_match_incr(pat, prev.prop, instsp)
                else:
                    for pat, prev in zip(As, prev_ths):
                        matcher.first_order_match_incr(pat, prev.prop, instsp)
                    matcher.first_order_match_incr(C, goal_th.prop, instsp)
            except matcher.MatchException:
                continue

            # All matches succeed
            t = logic.subst_norm(th.prop, instsp)
            As, C = t.strip_implies()

            results.append({"theorem": name, "_goal": As[len(prevs):]})
        return sorted(results, key = lambda d: d['theorem'])

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rule(), args=data['theorem'], prevs=prevs)

class introduction(Method):
    """Introducing variables and assumptions."""
    def __init__(self):
        self.sig = ["names"]

    def search(self, state, id, prevs):
        goal_th = state.get_proof_item(id).th
        if goal_th.prop.is_all():
            return [{}]
        elif goal_th.prop.is_implies():
            return [{"names": ""}]
        else:
            return []

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
        self.sig = ['s']

    def search(self, state, id, prevs):
        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            if prev_th.prop.is_all():
                return [{}]
            else:
                return []
        else:
            return []

    def apply(self, state, id, data, prevs):
        t = parser.parse_term(state.thy, state.get_ctxt(id), data['s'])
        state.add_line_before(id, 1)
        state.set_line(id, 'forall_elim', args=t, prevs=prevs)

class inst_exists_goal(Method):
    """Instantiate an exists goal."""
    def __init__(self):
        self.sig = ['s']

    def search(self, state, id, prev):
        cur_th = state.get_proof_item(id).th
        if logic.is_exists(cur_th.prop):
            return [{}]
        else:
            return []

    def apply(self, state, id, data, prevs):
        t = parser.parse_term(state.thy, state.get_ctxt(id), data['s'])
        state.apply_tactic(id, tactic.inst_exists_goal(), args=t, prevs=[])

class induction(Method):
    """Apply induction."""
    def __init__(self):
        self.sig = ['theorem', 'var']

    def search(self, state, id, prevs):
        cur_th = state.get_proof_item(id).th
        if len(cur_th.hyps) > 0:
            return []

        results = []
        for name, th in state.thy.get_data("theorems").items():
            if 'var_induct' not in state.thy.get_attributes(name):
                continue

            var_T = th.concl.arg.T
            vars = [v for v in term.get_vars(cur_th.prop) if v.T == var_T]
            if len(vars) == 1:
                results.append({'theorem': name, 'var': vars[0].name})
            elif len(vars) > 1:
                results.append({'theorem': name})
        return results

    def apply(self, state, id, data, prevs):
        # Find variable
        ctxt = state.get_ctxt(id)
        assert data['var'] in ctxt, "induction: cannot find variable."
        var = Var(data['var'], ctxt[data['var']])

        state.apply_tactic(id, tactic.var_induct(), args=(data['theorem'], var))


def apply_method(state, data):
    """Apply a method to the state. Here data is a dictionary containing
    all necessary information.

    """
    method = state.thy.get_method(data['method_name'])
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
    "inst_exists_goal": inst_exists_goal(),
    "induction": induction(),
})
