# Author: Bohua Zhan

from kernel import term
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ItemID, Proof, ProofException
from kernel.theory import Method
from kernel import theory
from logic.proofterm import ProofTermAtom
from logic import matcher
from logic import logic
from syntax import parser, printer, pprint, settings
from server import tactic


class cut_method(Method):
    """Insert intermediate goal."""
    def __init__(self):
        self.sig = ['goal']

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        goal = parser.parse_term(state.get_ctxt(id), data['goal'])
        return pprint.N("have ") + printer.print_term(state.thy, goal)

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        hyps = cur_item.th.hyps

        ctxt = state.get_ctxt(id)
        C = parser.parse_term(ctxt, data['goal'])
        for v in term.get_vars(C):
            if v.name not in ctxt.vars:
                raise AssertionError('Insert goal: extra variable %s' % v.name)

        state.add_line_before(id, 1)
        state.set_line(id, 'sorry', th=Thm(hyps, C))

class cases_method(Method):
    """Case analysis."""
    def __init__(self):
        self.sig = ['case']

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        A = parser.parse_term(state.get_ctxt(id), data['case'])
        return pprint.N("case ") + printer.print_term(state.thy, A)

    def apply(self, state, id, data, prevs):
        ctxt = state.get_ctxt(id)
        A = parser.parse_term(ctxt, data['case'])
        for v in term.get_vars(A):
            if v.name not in ctxt.vars:
                raise AssertionError('Apply case: extra variable %s' % v.name)

        state.apply_tactic(id, tactic.cases(), args=A)

class apply_prev_method(Method):
    """Apply previous fact."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs, data=None):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]
        try:
            pt = tactic.apply_prev().get_proof_term(state.thy, cur_item.th, args=None, prevs=prevs)
            return [{"_goal": [gap.prop for gap in pt.get_gaps()]}]
        except (AssertionError, matcher.MatchException):
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Apply fact (b)")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.apply_prev(), prevs=prevs)

class rewrite_goal_with_prev_method(Method):
    """Rewrite using previous fact."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs, data=None):
        try:
            cur_item = state.get_proof_item(id)
            prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]
            pt = tactic.rewrite_goal_with_prev().get_proof_term(state.thy, cur_item.th, args=None, prevs=prevs)
        except (AssertionError, matcher.MatchException):
            return []
        else:
            return [{"_goal": [gap.prop for gap in pt.get_gaps()]}]        

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("rewrite with fact")

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.rewrite_goal_with_prev(), prevs=prevs)

class rewrite_goal(Method):
    """Rewrite using a theorem."""
    def __init__(self):
        self.sig = ['theorem', 'sym']

    def search(self, state, id, prevs, data=None):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]

        thy = state.thy
        results = []

        def search_thm(th_name, sym):
            try:
                sym_b = True if sym == 'true' else False
                pt = tactic.rewrite_goal(sym=sym_b).get_proof_term(thy, cur_item.th, args=th_name, prevs=prevs)
                results.append({"theorem": th_name, "sym": sym, "_goal": [gap.prop for gap in pt.get_gaps()]})
            except (AssertionError, matcher.MatchException) as e:
                pass

        if data:
            sym = 'false'
            if 'sym' in data:
                sym = data['sym']
            search_thm(data['theorem'], sym)
        else:
            for th_name in thy.get_data("theorems"):
                if 'hint_rewrite' in thy.get_attributes(th_name):
                    search_thm(th_name, 'false')
                if 'hint_rewrite_sym' in thy.get_attributes(th_name):
                    search_thm(th_name, 'true')

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        if 'sym' in data and data['sym'] == 'true':
            return pprint.N(data['theorem'] + " (sym, r)")
        else:
            return pprint.N(data['theorem'] + " (r)")

    def apply(self, state, id, data, prevs):
        if 'sym' in data and data['sym'] == 'true':
            sym_b = True
        else:
            sym_b = False
        state.apply_tactic(id, tactic.rewrite_goal(sym=sym_b), args=data['theorem'], prevs=prevs)

class rewrite_fact(Method):
    """Rewrite fact using a theorem."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs, data=None):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]

        thy = state.thy
        results = []

        def search_thm(th_name):
            try:
                pt = logic.rewrite_fact_macro().get_proof_term(thy, th_name, prevs)
                results.append({"theorem": th_name, "_fact": [pt.prop]})
            except (AssertionError, matcher.MatchException):
                pass

        if data:
            search_thm(data['theorem'])
        else:
            for th_name in thy.get_data("theorems"):
                if 'hint_rewrite' in thy.get_attributes(th_name):
                    search_thm(th_name)

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N(data['theorem'] + " (r)")

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'rewrite_fact', args=data['theorem'], prevs=prevs)

        id2 = id.incr_id(1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)

class rewrite_fact_with_prev(Method):
    """Rewrite fact using a previous equality."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs, data=None):
        prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]
        try:
            macro = logic.rewrite_fact_with_prev_macro()
            pt = macro.get_proof_term(state.thy, args=None, pts=prevs)
            return [{"_fact": [pt.prop]}]
        except (AssertionError, matcher.MatchException):
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("rewrite fact with fact")

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'rewrite_fact_with_prev', prevs=prevs)

        id2 = id.incr_id(1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)

class apply_forward_step(Method):
    """Apply theorem in the forward direction."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs, data=None):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]

        thy = state.thy
        results = []

        def search_thm(th_name, min_prevs):
            if len(prevs) < min_prevs:
                return

            try:
                macro = logic.apply_theorem_macro()
                res_th = macro.eval(thy, th_name, prev_ths)
                results.append({"theorem": th_name, "_fact": [res_th.prop]})
            except theory.ParameterQueryException:
                results.append({"theorem": th_name})
            except (AssertionError, matcher.MatchException):
                pass

        if data:
            search_thm(data['theorem'], min_prevs=0)
        else:
            for th_name in thy.get_data("theorems"):
                if 'hint_forward' in thy.get_attributes(th_name):
                    search_thm(th_name, min_prevs=1)

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N(data['theorem'] + " (f)")

    def apply(self, state, id, data, prevs):
        inst = dict()
        thy = state.thy
        ctxt = state.get_ctxt(id)
        for key, val in data.items():
            if key.startswith("param_"):
                if val != '':
                    inst[key[6:]] = parser.parse_term(ctxt, val)

        th = thy.get_theorem(data['theorem'], svar=True)

        # Check whether to ask for parameters
        As, C = th.prop.strip_implies()
        match_svars = term.get_svars(As[:len(prevs)])
        all_svars = term.get_svars(th.prop)
        param_svars = [v for v in all_svars if v not in match_svars and 'param_' + v.name not in data]
        if param_svars:
            raise theory.ParameterQueryException(list("param_" + v.name for v in param_svars))

        # First test apply_theorem
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        macro = logic.apply_theorem_macro(with_inst=True)
        res_th = macro.eval(state.thy, (data['theorem'], dict(), inst), prev_ths)

        state.add_line_before(id, 1)
        if inst:
            state.set_line(id, 'apply_theorem_for', args=(data['theorem'], dict(), inst), prevs=prevs)
        else:
            state.set_line(id, 'apply_theorem', args=data['theorem'], prevs=prevs)

        id2 = id.incr_id(1)
        new_id = state.find_goal(state.get_proof_item(id2).th, id2)
        if new_id is not None:
            state.replace_id(id2, new_id)

class apply_backward_step(Method):
    """Apply theorem in the backward direction."""
    def __init__(self):
        self.sig = ['theorem']

    def search(self, state, id, prevs, data=None):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]

        thy = state.thy
        results = []

        def search_thm(th_name):
            try:
                pt = tactic.rule().get_proof_term(thy, cur_item.th, args=th_name, prevs=prevs)
                results.append({"theorem": th_name, "_goal": [gap.prop for gap in pt.get_gaps()]})
            except theory.ParameterQueryException:
                # In this case, still suggest the result
                results.append({"theorem": th_name})
            except (AssertionError, matcher.MatchException):
                pass

        if data:
            search_thm(data['theorem'])
        else:
            for th_name in thy.get_data("theorems"):
                if 'hint_backward' in thy.get_attributes(th_name) or \
                   ('hint_backward1' in thy.get_attributes(th_name) and len(prevs) >= 1):
                    search_thm(th_name)

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N(data['theorem'] + " (b)")

    def apply(self, state, id, data, prevs):
        inst = dict()
        ctxt = state.get_ctxt(id)
        for key, val in data.items():
            if key.startswith("param_"):
                inst[key[6:]] = parser.parse_term(ctxt, val)
        if inst:
            state.apply_tactic(id, tactic.rule(), args=(data['theorem'], (dict(), inst)), prevs=prevs)
        else:
            state.apply_tactic(id, tactic.rule(), args=data['theorem'], prevs=prevs)

class apply_resolve_step(Method):
    """Resolve using a theorem ~A and a fact A."""
    def __init__(self):
        self.sig = ["theorem"]

    def search(self, state, id, prevs, data=None):
        cur_item = state.get_proof_item(id)
        prevs = [ProofTermAtom(prev, state.get_proof_item(prev).th) for prev in prevs]

        thy = state.thy
        results = []

        def search_thm(th_name):
            try:
                pt = tactic.resolve().get_proof_term(thy, cur_item.th, args=th_name, prevs=prevs)
                results.append({"theorem": th_name, "_goal": [gap.prop for gap in pt.get_gaps()]})
            except (AssertionError, matcher.MatchException):
                pass

        if data:
            search_thm(data['theorem'])
        else:
            for th_name in thy.get_data("theorems"):
                if 'hint_resolve' in thy.get_attributes(th_name):
                    search_thm(th_name)

        return sorted(results, key=lambda d: d['theorem'])

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Resolve using " + data['theorem'])

    def apply(self, state, id, data, prevs):
        state.apply_tactic(id, tactic.resolve(), args=data['theorem'], prevs=prevs)

class introduction(Method):
    """Introducing variables and assumptions."""
    def __init__(self):
        self.sig = []

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        goal_th = state.get_proof_item(id).th
        if goal_th.prop.is_all():
            return [{}]
        elif goal_th.prop.is_implies():
            return [{"names": ""}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        res = "introduction"
        if 'names' in data and data['names'] != "":
            names = [name.strip() for name in data['names'].split(',')]
            if len(names) > 1:
                res += " with names " + ", ".join(names)
            else:
                res += " with name " + ", ".join(names)
        return pprint.N(res)

    def apply(self, state, id, data, prevs):
        cur_item = state.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"

        prop = cur_item.th.prop
        assert prop.is_implies() or prop.is_all(), "introduction"

        if prop.is_all() and 'names' not in data:
            raise theory.ParameterQueryException(['names'])

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

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            if logic.is_exists(prev_th.prop):
                return [{}]

        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Instantiate exists fact")

    def apply(self, state, id, data, prevs):
        assert len(prevs) == 1, "exists_elim"

        # Parse the list of variable names
        ctxt = state.get_ctxt(id)
        names = [name.strip() for name in data['names'].split(',')]
        for name in names:
            if name in ctxt.vars:
                raise AssertionError("Instantiate exists: duplicate name %s" % name)

        exists_item = state.get_proof_item(prevs[0])
        exists_prop = exists_item.th.prop
        assert logic.is_exists(exists_prop), "exists_elim"

        vars, body = logic.strip_exists(exists_prop, names)

        # Add one line for each variable, and one line for body of exists
        state.add_line_before(id, len(vars) + 1)
        for i, var in enumerate(vars):
            state.set_line(id.incr_id(i), 'variable', args=(var.name, var.T), prevs=[])
        state.set_line(id.incr_id(len(vars)), 'assume', args=body, prevs=[])

        # Find the intros at the end, append exists fact and new variables
        # and assumptions to prevs.
        new_intros = [prevs[0]] + [id.incr_id(i) for i in range(len(vars)+1)]
        i = len(vars) + 1
        while True:
            try:
                item = state.get_proof_item(id.incr_id(i))
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
                    state.set_line(id.incr_id(i), item.rule, args=item.args, prevs=item.prevs, \
                                   th=Thm(list(item.th.hyps) + [body], item.th.prop))
            i += 1


class forall_elim(Method):
    """Elimination of forall statement."""
    def __init__(self):
        self.sig = ['s']

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) == 1:
            prev_th = state.get_proof_item(prevs[0]).th
            if prev_th.prop.is_all():
                return [{}]

        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Forall elimination")

    def apply(self, state, id, data, prevs):
        ctxt = state.get_ctxt(id)
        t = parser.parse_term(ctxt, data['s'])

        for v in term.get_vars(t):
            if v.name not in ctxt.vars:
                raise AssertionError('Forall elimination: extra variable %s' % v.name)

        state.add_line_before(id, 1)
        state.set_line(id, 'forall_elim', args=t, prevs=prevs)

class inst_exists_goal(Method):
    """Instantiate an exists goal."""
    def __init__(self):
        self.sig = ['s']

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        if len(prevs) > 0:
            return []

        cur_th = state.get_proof_item(id).th
        if logic.is_exists(cur_th.prop):
            return [{}]
        else:
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Instantiate exists goal")

    def apply(self, state, id, data, prevs):
        ctxt = state.get_ctxt(id)
        t = parser.parse_term(ctxt, data['s'])

        for v in term.get_vars(t):
            if v.name not in ctxt.vars:
                raise AssertionError('Instantiate exists: extra variable %s' % v.name)

        state.apply_tactic(id, tactic.inst_exists_goal(), args=t, prevs=[])

class induction(Method):
    """Apply induction."""
    def __init__(self):
        self.sig = ['theorem', 'var']

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

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
            return pprint.N("Induction " + data['theorem'] + " var: " + data['var'])
        else:
            return pprint.N("Induction " + data['theorem'])

    def apply(self, state, id, data, prevs):
        # Find variable
        ctxt = state.get_ctxt(id)
        assert data['var'] in ctxt.vars, "induction: cannot find variable."
        var = Var(data['var'], ctxt.vars[data['var']])

        state.apply_tactic(id, tactic.var_induct(), args=(data['theorem'], var))

class new_var(Method):
    """Create new variable."""
    def __init__(self):
        self.sig = ['name', 'type']

    def search(self, state, id, prevs, data=None):
        if data:
            return [data]

        return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        T = parser.parse_type(state.thy, data['type'])
        return pprint.N("Variable " + data['name'] + " :: ") + printer.print_type(state.thy, T)

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

    def search(self, state, id, prevs, data=None):
        prev_ths = [state.get_proof_item(prev).th for prev in prevs]
        thy = state.thy

        try:
            macro = logic.apply_fact_macro()
            pt = macro.eval(thy, args=None, prevs=prev_ths)
            return [{"_fact": [pt.prop]}]
        except (AssertionError, matcher.MatchException):
            return []

    @settings.with_settings
    def display_step(self, state, id, data, prevs):
        return pprint.N("Apply fact (f) " + str(prevs[0]) + " onto " + \
                         ", ".join(str(id) for id in prevs[1:]))

    def apply(self, state, id, data, prevs):
        state.add_line_before(id, 1)
        state.set_line(id, 'apply_fact', prevs=prevs)


def apply_method(state, step):
    """Apply a method to the state. Here data is a dictionary containing
    all necessary information.

    """
    method = state.thy.get_method(step['method_name'])
    goal_id = ItemID(step['goal_id'])
    fact_ids = [ItemID(fact_id) for fact_id in step['fact_ids']] \
        if 'fact_ids' in step and step['fact_ids'] else []
    return method.apply(state, goal_id, step, fact_ids)

@settings.with_settings
def display_method(state, step, mode='long'):
    """Obtain the string explaining the step in the user interface."""
    method = theory.global_methods[step['method_name']]
    goal_id = ItemID(step['goal_id'])
    fact_ids = [ItemID(fact_id) for fact_id in step['fact_ids']] \
        if 'fact_ids' in step and step['fact_ids'] else []
    search_res = method.search(state, goal_id, fact_ids, data=step)
    assert len(search_res) == 1, "display_method: %s, %d result found." % (
        step['method_name'], len(search_res))

    return method.output_step(state, goal_id, search_res[0], fact_ids, mode=mode)


theory.global_methods.update({
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
