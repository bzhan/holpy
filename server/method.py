# Author: Bohua Zhan

from kernel import term
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import id_force_tuple, print_id, Proof, ProofException
from kernel.theory import Method, global_methods
from logic.conv import top_conv, rewr_conv, beta_conv, then_conv, top_sweep_conv
from logic.proofterm import ProofTermAtom
from logic import matcher
from logic import logic
from syntax import parser, printer, settings
from server import tactic

def incr_id(id, n):
    """Increment the last number in id by n."""
    return id[:-1] + (id[-1] + n,)

def display_goals(state, data):
    """Return list of goals in string form. If there is no goals
    remaining, return '(solves)'.

    """
    assert '_goal' in data, "display_goals"
    if data['_goal']:
        goals = [printer.print_term(state.thy, t) for t in data['_goal']]
        return printer.commas_join(goals)
    else:
        return printer.N("(solves)")

def display_facts(state, data):
    """Return list of new facts in string form."""
    assert '_fact' in data and len(data['_fact']) > 0, "display_facts"
    facts = [printer.print_term(state.thy, t) for t in data['_fact']]
    return printer.N("have ") + printer.commas_join(facts)


class cut_method(Method):
    """Insert intermediate goal."""
    def __init__(self):
        self.sig = ['goal']

    def search(self, state, id, prevs):
        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("have ") + data['goal']

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        hyps = cur_item.th.hyps

        goal = parser.parse_term(state.thy, state.get_ctxt(id), data['goal'])

        state.add_line_before(id, 1)
        state.set_line(id, 'sorry', th=Thm(hyps, goal))

class cases_method(Method):
    """Case analysis."""
    def __init__(self):
        self.sig = ['case']

    def search(self, state, id, prevs):
        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("case ") + data['case']

    def apply(self, state, id, data, prevs):
        A = parser.parse_term(state.thy, state.get_ctxt(id), data['case'])
        state.apply_tactic(id, tactic.cases(), args=A)

class apply_prev_method(Method):
    """Apply previous fact."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        try:
            id = id_force_tuple(id)
            prevs = [id_force_tuple(prev) for prev in prevs] if prevs else []
            prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]
            cur_item = state.get_proof_item(id)
            pt = tactic.apply_prev().get_proof_term(state.thy, cur_item.th, args=None, prevs=prevs)
        except (AssertionError, matcher.MatchException):
            return []
        else:
            return [{"_goal": [gap.prop for gap in pt.get_gaps()]}]

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("Apply fact (b): ") + display_goals(state, data)

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
        cv = then_conv(top_sweep_conv(rewr_conv(pt, match_vars=False)),
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

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("rewrite with fact: ") + display_goals(state, data)

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

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N(data['theorem'] + " (r): ") + display_goals(state, data)

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rewrite(), args=data['theorem'])

class rewrite_fact(Method):
    """Rewrite fact using a theorem."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs):
        if len(prevs) != 1:
            return []

        prev_th = state.get_proof_item(prevs[0]).th
        thy = state.thy
        results = []
        for th_name, th in thy.get_data("theorems").items():
            if 'hint_rewrite' not in thy.get_attributes(th_name):
                continue

            cv = top_sweep_conv(rewr_conv(th_name))
            th = cv.eval(thy, prev_th.prop)
            new_fact = th.prop.rhs
            if prev_th.prop != new_fact:
                results.append({"theorem": th_name, "_fact": [new_fact]})

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N(data['theorem'] + " (r): ") + display_facts(state, data)

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'rewrite_fact', args=data['theorem'], prevs=prevs)

class rewrite_fact_with_prev(Method):
    """Rewrite fact using a previous equality."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        if len(prevs) != 2:
            return []

        eq_th, prev_th = [state.get_proof_item(prev).th for prev in prevs]
        if not eq_th.prop.is_equals():
            return []

        cv = top_sweep_conv(rewr_conv(ProofTermAtom(prevs[0], eq_th), match_vars=False))
        th = cv.eval(state.thy, prev_th.prop)
        new_fact = th.prop.rhs
        if prev_th.prop != new_fact:
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("rewrite fact with fact")

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'rewrite_fact_with_prev', prevs=prevs)

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
        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N(data['theorem'] + " (f): ") + display_facts(state, data)

    def apply(self, state, id, data, prevs):
        assert prevs, "apply_forward_step: prevs is not empty"
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_theorem', args=data['theorem'], prevs=prevs)

        id2 = incr_id(id, 1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)

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
        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N(data['theorem'] + " (b): ") + display_goals(state, data)

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rule(), args=data['theorem'], prevs=prevs)

class apply_resolve_step(Method):
    """Resolve using a theorem ~A and a fact A."""
    def __init__(self):
        self.sig = ["theorem"]

    def search(self, state, id, prevs):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        if len(prev_ths) != 1:
            return []

        thy = state.thy

        results = []
        for name, th in thy.get_data("theorems").items():
            if 'hint_resolve' not in thy.get_attributes(name):
                continue

            assert logic.is_neg(th.prop), "apply_resolve_step"

            try:
                matcher.first_order_match(th.prop.arg, prev_ths[0].prop)
            except matcher.MatchException:
                continue

            results.append({"theorem": name, "_goal": []})
        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("Resolve using " + data['theorem'])

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.resolve(), args=data['theorem'], prevs=prevs)

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

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        res = "introduction on " + print_id(id)
        if 'names' in data and data['names'] != "":
            res += " with names " + data['names']
        return printer.N(res)

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"

        prop = cur_item.th.prop
        assert prop.is_implies() or prop.is_all(), "introduction"

        intros_tac = tactic.intros()
        if 'names' in data and data['names'] != '':
            names = [name.strip() for name in data['names'].split(",")]
        else:
            names = []
        pt = intros_tac.get_proof_term(state.thy, cur_item.th, args=names)

        cur_item.rule = "subproof"
        cur_item.subproof = pt.export(prefix=id)
        state.check_proof(compute_only=True)

        # Test if the goal is already proved
        for item in cur_item.subproof.items:
            new_id = state.find_goal(state.get_proof_item(item.id).th, item.id)
            if new_id is not None:
                state.replace_id(item.id, new_id)

class exists_elim(Method):
    """Make use of an exists fact."""
    def __init__(self):
        self.sig = ['names']

    def search(self, state, id, prevs):
        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            if logic.is_exists(prev_th.prop):
                return [{}]
            else:
                return []
        else:
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("Instantiate exists fact")

    def apply(self, state, id, data, prevs):
        # Parse the list of variable names
        names = [name.strip() for name in data['names'].split(',')]
        assert len(prevs) == 1, "exists_elim"

        exists_item = state.get_proof_item(prevs[0])
        exists_prop = exists_item.th.prop
        assert logic.is_exists(exists_prop), "exists_elim"

        vars, body = logic.strip_exists(exists_prop, names)

        # Add one line for each variable, and one line for body of exists
        state.add_line_before(id, len(vars) + 1)
        for i, var in enumerate(vars):
            state.set_line(incr_id(id, i), 'variable', args=(var.name, var.T), prevs=[])
        state.set_line(incr_id(id, len(vars)), 'assume', args=body, prevs=[])

        # Find the intros at the end, append exists fact and new variables
        # and assumptions to prevs.
        new_intros = [prevs[0]] + [incr_id(id, i) for i in range(len(vars)+1)]
        i = len(vars) + 1
        while True:
            try:
                item = state.get_proof_item(incr_id(id, i))
            except ProofException:
                raise AssertionError("exists_elim: cannot find intros at the end")
            else:
                if item.rule == 'intros':
                    if item.args is None:
                        item.args = [exists_prop]
                    else:
                        item.args = [exists_prop] + item.args
                    item.prevs = item.prevs[:-1] + new_intros + [item.prevs[-1]]
                    break
                else:
                    state.set_line(incr_id(id, i), item.rule, args=item.args, prevs=item.prevs, \
                                   th=Thm(list(item.th.hyps) + [body], item.th.prop))
            i += 1


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

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("forall elimination")

    def apply(self, state, id, data, prevs):
        t = parser.parse_term(state.thy, state.get_ctxt(id), data['s'])
        state.add_line_before(id, 1)
        state.set_line(id, 'forall_elim', args=t, prevs=prevs)

class inst_exists_goal(Method):
    """Instantiate an exists goal."""
    def __init__(self):
        self.sig = ['s']

    def search(self, state, id, prevs):
        if len(prevs) > 0:
            return []

        cur_th = state.get_proof_item(id).th
        if logic.is_exists(cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("instantiate exists goal")

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

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        if 'var' in data:
            return printer.N("induction " + data['theorem'] + " var: " + data['var'])
        else:
            return printer.N("induction " + data['theorem'])

    def apply(self, state, id, data, prevs):
        # Find variable
        ctxt = state.get_ctxt(id)
        assert data['var'] in ctxt['vars'], "induction: cannot find variable."
        var = Var(data['var'], ctxt['vars'][data['var']])

        state.apply_tactic(id, tactic.var_induct(), args=(data['theorem'], var))

class new_var(Method):
    """Create new variable."""
    def __init__(self):
        self.sig = ['name', 'type']

    def search(self, state, id, prevs):
        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("variable " + data['name'] + " :: ") + printer.print_type(state.thy, data['type'])

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        T = parser.parse_type(state.thy, data['type'])
        state.set_line(id, 'variable', args=(data['name'], T), prevs=[])

class apply_fact(Method):
    """When one of the prevs is an forall/implies fact, apply that fact
    to the remaining prevs.

    """
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        thy = state.thy
        if len(prevs) < 2:
            return []

        th, prev_ths = prev_ths[0], prev_ths[1:]

        # First, obtain the patterns
        vars = term.get_vars(th.prop)
        new_names = logic.get_forall_names(th.prop)
        assert {v.name for v in vars}.isdisjoint(set(new_names)), "apply_fact: name conflict"
        new_vars, As, C = logic.strip_all_implies(th.prop, new_names)
        if len(prev_ths) > len(As):
            return []

        instsp = dict(), {v.name: v for v in vars}
        try:
            for idx, prev_th in enumerate(prev_ths):
                matcher.first_order_match_incr(As[idx], prev_th.prop, instsp)
        except matcher.MatchException:
            return []

        return [{}]

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return printer.N("Apply fact (f) " + print_id(prevs[0]) + " onto " + \
            ", ".join(print_id(id) for id in prevs[1:]))

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_fact', prevs=prevs)


def apply_method(state, data):
    """Apply a method to the state. Here data is a dictionary containing
    all necessary information.

    """
    method = state.thy.get_method(data['method_name'])
    goal_id = id_force_tuple(data['goal_id'])
    fact_ids = [id_force_tuple(fact_id) for fact_id in data['fact_ids']] \
        if 'fact_ids' in data and data['fact_ids'] else []
    return method.apply(state, goal_id, data, fact_ids)

def display_method(state, step):
    method = global_methods[step['method_name']]
    goal_id = id_force_tuple(step['goal_id'])
    fact_ids = [id_force_tuple(fact_id) for fact_id in step['fact_ids']] \
        if 'fact_ids' in step and step['fact_ids'] else []
    search_res = method.search(state, goal_id, fact_ids)
    if 'no_search' in step:
        return method.display_step(state, goal_id, step, fact_ids)
    else:
        for res in search_res:
            if all(sig not in res or res[sig] == step[sig] for sig in method.sig):
                return method.display_step(state, goal_id, res, fact_ids)


global_methods.update({
    "cut": cut_method(),
    "cases": cases_method(),
    "apply_prev": apply_prev_method(),
    "rewrite_goal_with_prev": rewrite_goal_with_prev_method(),
    "rewrite_goal": rewrite_goal(),
    "rewrite_fact": rewrite_fact(),
    "rewrite_fact_with_prev": rewrite_fact_with_prev(),
    "apply_forward_step": apply_forward_step(),
    "apply_backward_step": apply_backward_step(),
    "apply_resolve_step": apply_resolve_step(),
    "apply_fact": apply_fact(),
    "introduction": introduction(),
    "forall_elim": forall_elim(),
    "exists_elim": exists_elim(),
    "inst_exists_goal": inst_exists_goal(),
    "induction": induction(),
    "new_var": new_var(),
})
