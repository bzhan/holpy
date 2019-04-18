# Author: Bohua Zhan

import io

from kernel import term
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import ProofItem, Proof, id_force_tuple
from kernel import report
from logic import logic, matcher
from logic.proofterm import ProofTerm
from logic.conv import top_conv, rewr_conv, then_conv, beta_conv
from syntax import parser, printer


class TacticException(Exception):
    pass

# Helper functions

def incr_id_after(id, start, n):
    """Perform the id adjustment necessary for adding n lines before
    start id. The exact logic is as follows:
    
    Suppose start has length k. Find all ids with length at least k,
    where the first k-1 numbers agree with start, and the k'th number
    is greater than or equal to start. Increment the k'th number by n
    and leave the rest unchanged.

    """
    k = len(start)
    if len(id) >= k and id[:k-1] == start[:k-1] and id[k-1] >= start[k-1]:
        return id[:k-1] + (id[k-1] + n,) + id[k:]
    else:
        return id

def incr_proof_item(item, start, n):
    """Increment all ids in the given proof item. Recursively increment
    ids in subproofs.
    
    """
    item.id = incr_id_after(item.id, start, n)
    item.prevs = [incr_id_after(id, start, n) for id in item.prevs]
    if item.subproof:
        for subitem in item.subproof.items:
            incr_proof_item(subitem, start, n)

def decr_id(id, id_remove):
    """Decrement a single id, with the aim of closing the gap at
    id_remove. The logic used is similar to that incr_id_after.
    
    """
    k = len(id_remove)
    if len(id) >= k and id[:k-1] == id_remove[:k-1] and id[k-1] > id_remove[k-1]:
        return id[:k-1] + (id[k-1] - 1,) + id[k:]
    else:
        return id

def decr_proof_item(item, id_remove):
    """Decrement all ids in the given proof item."""
    item.id = decr_id(item.id, id_remove)
    item.prevs = [decr_id(id, id_remove) for id in item.prevs]
    if item.subproof:
        for subitem in item.subproof.items:
            decr_proof_item(subitem, id_remove)

def incr_id(id, n):
    """Increment the last number in id by n."""
    return id[:-1] + (id[-1] + n,)


class ProofState():
    """Represents proof state on the server side."""

    def __init__(self, thy):
        """Empty proof state."""
        self.thy = thy
        self.vars = []
        self.prf = Proof()

    def get_ctxt(self, id):
        """Obtain the context at the given id."""
        id = id_force_tuple(id)
        ctxt = {}
        for v in self.vars:
            ctxt[v.name] = v.T

        prf = self.prf
        try:
            for n in id:
                for item in prf.items[:n]:
                    if item.rule == "variable":
                        nm, T = item.args
                        ctxt[nm] = T
                prf = prf.items[n].subproof
            return ctxt
        except (AttributeError, IndexError):
            raise TacticException()

    def __str__(self):
        vars = sorted(self.vars, key = lambda v: v.name)
        lines = "\n".join('var ' + v.name + ' :: ' + str(v.T) for v in vars)
        return lines + "\n" + str(self.prf)

    @staticmethod
    def init_state(thy, vars, assums, concl):
        """Construct initial partial proof for the given assumptions and
        conclusion.

        assums - assumptions A1, ... An.
        concl - conclusion C.
        
        Constructs:

        0: assume A1
        ...
        n-1: assume An
        n: C by sorry
        n+1: An --> C by implies_intr n-1 from n
        ...
        2n: A1 --> ... --> An --> C by implies_intr 0 from 2n-1.

        """
        assert all(isinstance(var, Term) for var in vars), "init_state: vars must be terms."
        assert all(isinstance(a, Term) for a in assums), "init_state: assums must be terms."
        assert isinstance(concl, Term), "init_state: conclusion must be a term."
        state = ProofState(thy)

        state.vars = vars
        state.prf = Proof(*assums)
        n = len(assums)
        state.prf.add_item(n, "sorry", th=Thm(assums, concl))
        for i, assum in enumerate(reversed(assums), 0):
            state.prf.add_item(n + i + 1, "implies_intr", args=assum, prevs=[n+i])
        state.check_proof(compute_only=True)
        return state

    @staticmethod
    def parse_init_state(thy, data):
        """Given data for a theorem statement, construct the initial partial proof.
        
        data['vars']: list of variables.
        data['prop']: proposition to be proved. In the form A1 --> ... --> An --> C.

        """
        ctxt = {}
        vars = []
        for name, str_T in data['vars'].items():
            T = parser.parse_type(thy, str_T)
            vars.append(Var(name, T))
            ctxt[name] = T
        prop = parser.parse_term(thy, ctxt, data['prop'])
        assums, concl = prop.strip_implies()

        return ProofState.init_state(thy, vars, assums, concl)

    def json_data(self):
        """Export proof in json format."""
        self.check_proof()
        return {
            "vars": [{'name': v.name, 'T': str(v.T)} for v in self.vars],
            "proof": sum([printer.export_proof_item(self.thy, item, unicode=True, highlight=True)
                          for item in self.prf.items], []),
            "report": self.rpt.json_data()
        }

    @staticmethod
    def parse_proof(thy, data):
        """Obtain proof from json format."""
        ctxt = {}
        state = ProofState(thy)
        for name, str_T in data['vars'].items():
            T = parser.parse_type(thy, str_T)
            state.vars.append(Var(name, T))
            ctxt[name] = T
        state.prf = Proof()
        for line in data['proof']:
            item = parser.parse_proof_rule(thy, ctxt, line)
            state.prf.insert_item(item)
            if item.rule == "variable":
                nm, T = item.args
                ctxt[nm] = T

        state.check_proof(compute_only=True)
        return state

    def check_proof(self, *, no_gaps=False, compute_only=False):
        """Check the given proof. Report is stored in rpt."""
        self.rpt = report.ProofReport()
        return self.thy.check_proof(self.prf, rpt=self.rpt, no_gaps=no_gaps, compute_only=compute_only)

    def add_line_after(self, id):
        """Add given line after the given id."""
        id = id_force_tuple(id)
        prf = self.prf.get_parent_proof(id)
        new_id = incr_id(id, 1)
        split = new_id[-1]
        prf.items = prf.items[:split] + [ProofItem(new_id, "")] + prf.items[split:]
        for item in prf.items[split+1:]:
            incr_proof_item(item, new_id, 1)

        self.check_proof(compute_only=True)

    def add_line_before(self, id, n):
        """Add n lines before the given id."""
        id = id_force_tuple(id)
        prf = self.prf.get_parent_proof(id)
        split = id[-1]
        new_items = [ProofItem(incr_id(id, i), "") for i in range(n)]
        prf.items = prf.items[:split] + new_items + prf.items[split:]
        for item in prf.items[split+n:]:
            incr_proof_item(item, id, n)

        self.check_proof(compute_only=True)

    def remove_line(self, id):
        """Remove line with the given id."""
        id = id_force_tuple(id)
        prf = self.prf.get_parent_proof(id)
        split = id[-1]
        prf.items = prf.items[:split] + prf.items[split+1:]
        for item in prf.items[split:]:
            decr_proof_item(item, id)

        self.check_proof(compute_only=True)

    def set_line(self, id, rule, *, args=None, prevs=None, th=None):
        """Set the item with the given id to the following data."""
        id = id_force_tuple(id)
        prf = self.prf.get_parent_proof(id)
        prf.items[id[-1]] = ProofItem(id, rule, args=args, prevs=prevs, th=th)
        self.check_proof(compute_only=True)

    def get_proof_item(self, id):
        """Obtain the proof item with the given id."""
        return self.prf.find_item(id)

    def replace_id(self, old_id, new_id):
        """Replace old_id with new_id in prevs."""
        def replace(prf):
            for item in prf.items:
                item.prevs = [new_id if id == old_id else id for id in item.prevs]
                if item.subproof:
                    replace(item.subproof)

        prf = self.prf.get_parent_proof(old_id)
        replace(prf)

        self.remove_line(old_id)

    def find_goal(self, concl, goal_id):
        """Determine if the given conclusion is already proved,
        for the purpose of showing goal_id.

        Proof items that can be used include all items with id
        whose length is at most that of goal_id, where all but
        the last number agrees with that of goal_id, and the
        last number is less than the corresponding number in goal_id.

        """
        prf = self.prf
        try:
            for n in goal_id:
                for item in prf.items[:n]:
                    if item.th is not None and item.th.can_prove(concl):
                        return item.id
                prf = prf.items[n].subproof
        except (AttributeError, IndexError):
            raise TacticException()

    def apply_backward_step_thms(self, id, prevs=None):
        """Return the list of theorems that can be used for applying
        backward step.

        This is done by first matching each of the prevs against the
        assumptions in order, then match the conclusion.

        """
        id = id_force_tuple(id)
        prevs = [id_force_tuple(prev) for prev in prevs] if prevs else []
        prevs = [self.get_proof_item(id) for id in prevs]

        # Obtain the statement to be proved.
        cur_item = self.get_proof_item(id)
        if cur_item.rule != "sorry":
            return []

        results = []
        for name, th in self.thy.get_data("theorems").items():
            if 'hint_backward' not in self.thy.get_attributes(name):
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
            if not prevs and term.get_consts(C) == []:
                continue

            try:
                for pat, prev in zip(As, prevs):
                    matcher.first_order_match_incr(pat, prev.th.prop, instsp)
                matcher.first_order_match_incr(C, cur_item.th.prop, instsp)
            except matcher.MatchException:
                continue

            # All matches succeed
            t = logic.subst_norm(th.prop, instsp)
            t = printer.print_term(self.thy, t)
            results.append((name, t))
        return sorted(results)

    def apply_backward_step(self, id, th_name, *, prevs=None, instsp=None):
        """Apply backward step using the given theorem.
        
        prevs - list of previous proved facts to use.
        inst - existing instantiation.

        """
        id = id_force_tuple(id)
        prevs = [id_force_tuple(prev) for prev in prevs] if prevs else []

        # Obtain the statement to be proved.
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_backward_step: id is not a gap"

        # Instantiate the given theorem.
        th = self.thy.get_theorem(th_name)

        if instsp is None:
            instsp = (dict(), dict())
            As, C = th.assums, th.concl
            for pat, prev in zip(As, prevs):
                item = self.get_proof_item(prev)
                matcher.first_order_match_incr(pat, item.th.prop, instsp)
            matcher.first_order_match_incr(C, cur_item.th.prop, instsp)

        As, _ = logic.subst_norm(th.prop, instsp).strip_implies()

        num_goal = len(As) - len(prevs)
        self.add_line_before(id, num_goal)
        start = id
        all_ids = [incr_id(start, i - len(prevs)) for i in range(len(prevs), len(As))]
        for goal_id, A in zip(all_ids, As[len(prevs):]):
            self.set_line(goal_id, "sorry", th=Thm(cur_item.th.hyps, A))

        tyinst, inst = instsp
        self.set_line(incr_id(start, num_goal), "apply_theorem_for",
                      args=(th_name, tyinst, inst), prevs=prevs + all_ids, th=cur_item.th)

        # Test if the goals are already proved:
        for goal_id, A in reversed(list(zip(all_ids, As[len(prevs):]))):
            goal = Thm(cur_item.th.hyps, A)
            new_id = self.find_goal(goal, goal_id)
            if new_id is not None:
                self.replace_id(goal_id, new_id)

    def get_poorf_items(self, ids):
        return [self.prf.find_item(id) for id in ids] if ids else []

    def check_items_concl(self, items):
        for item in items:
            if item.rule == 'sorry' or item.th is None:
                return False

        return True

    def apply_forward_step_thms(self, id, prevs=None):
        id = id_force_tuple(id)
        prevs = [id_force_tuple(prev) for prev in prevs] if prevs else []

        if prevs:
            cur_items = self.get_poorf_items(prevs)
            if not self.check_items_concl(cur_items):
                return []
        else:
            return []

        prevs = [self.get_proof_item(id) for id in prevs]

        results = []
        for name, th in self.thy.get_data("theorems").items():
            if 'hint_forward' not in self.thy.get_attributes(name):
                continue

            instsp = (dict(), dict())
            As, C = th.assums, th.concl

            if len(prevs) != len(As):
                continue

            if set(term.get_vars(As)) != set(term.get_vars(As + [C])):
                continue

            if not term.get_consts(As):
                continue

            try:
                for pat, prev in zip(As, prevs):
                    matcher.first_order_match_incr(pat, prev.th.concl, instsp)
            except matcher.MatchException:
                continue

            # All matches succeed
            t = logic.subst_norm(th.prop, instsp)
            t = printer.print_term(self.thy, t)
            results.append((name, t))
        return sorted(results)

    def apply_forward_step(self, id, th_name, prevs=None, instsp=None):
        """Apply forward step using the given theorem.

        prevs - list of previous proved facts to use.
        inst - existing instantiation.

        """
        id = id_force_tuple(id)
        prevs = [id_force_tuple(prev) for prev in prevs] if prevs else []

        assert prevs, "apply_forward_step: prevs is not empty"

        self.add_line_before(id, 1)
        self.set_line(id, 'apply_theorem', args=th_name, prevs=prevs)

    def introduction(self, id, names=None):
        """Introduce assumptions for a goal of the form

        !x_1 ... x_k. A_1 --> ... --> A_n --> C.

        Argument names specifies list of variable names.
        
        """
        id = id_force_tuple(id)
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "introduction: id is not a gap"

        if names is None:
            names = []

        vars, As, C = logic.strip_all_implies(cur_item.th.prop, names)

        cur_item.rule = "subproof"
        cur_item.subproof = Proof()
        subprf = cur_item.subproof

        # Variables
        for i, var in enumerate(vars):
            cur_id = id + (i,)
            subprf.add_item(cur_id, "variable", args=(var.name, var.T))

        # Assumptions
        for i, A in enumerate(As):
            cur_id = id + (len(vars) + i,)
            subprf.add_item(cur_id, "assume", args=A, th=Thm([A], A))

        # Goal
        goal = Thm(list(cur_item.th.hyps) + As, C)
        goal_id = id + (len(vars) + len(As), )
        subprf.add_item(goal_id, "sorry", th=goal)

        # implies_intr invocations
        for i, A in enumerate(reversed(As)):
            cur_id = id + (len(vars) + len(As) + i + 1,)
            prev_id = id + (len(vars) + len(As) + i,)
            subprf.add_item(cur_id, "implies_intr", args=A, prevs=[prev_id])

        # forall_intr invocations
        for i, var in enumerate(reversed(vars)):
            cur_id = id + (len(vars) + 2 * len(As) + i + 1,)
            prev_id = id + (len(vars) + 2 * len(As) + i,)
            subprf.add_item(cur_id, "forall_intr", args=var, prevs=[prev_id])

        # Test if the goal is already proved
        new_id = self.find_goal(goal, goal_id)
        if new_id is not None:
            self.replace_id(goal_id, new_id)

    def apply_induction(self, id, th_name, var):
        """Apply induction using the given theorem and on the given
        variable.
        
        """
        id = id_force_tuple(id)
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "apply_induction: id is not a gap"

        # Find variable
        assert isinstance(var, str), "apply_induction: input must be a string"
        for v in self.vars:
            if v.name == var:
                var = v
                break

        assert not isinstance(var, str), "apply_induction: variable not found"

        # Current goal
        goal = cur_item.th.prop

        # Instantiation for P
        P = Term.mk_abs(var, goal)
        inst = {"P": P, "x": var}
        self.apply_backward_step(id, th_name, instsp=({}, inst))

    def rewrite_goal_thms(self, id):
        """Find list of theorems on which rewrite_goal can be applied."""

        id = id_force_tuple(id)
        cur_item = self.get_proof_item(id)
        if cur_item.rule != "sorry":
            return []

        results = []
        goal = cur_item.th.prop
        for th_name, th in self.thy.get_data("theorems").items():
            if 'hint_rewrite' not in self.thy.get_attributes(th_name):
                continue

            cv = top_conv(rewr_conv(th_name))
            new_goal = cv.eval(self.thy, goal).prop.rhs
            if goal != new_goal:
                new_goal = printer.print_term(self.thy, new_goal)
                results.append((th_name, new_goal))

        return sorted(results)

    def rewrite_goal(self, id, th_name, *, backward=False):
        """Apply an existing equality theorem to the given goal."""

        id = id_force_tuple(id)
        cur_item = self.get_proof_item(id)
        assert cur_item.rule == "sorry", "rewrite_goal: id is not a gap"

        init_As = cur_item.th.hyps
        goal = cur_item.th.prop
        cv = then_conv(top_conv(rewr_conv(th_name)),
                       top_conv(beta_conv()))
        new_goal = cv.eval(self.thy, goal).prop.rhs

        new_As = list(set(cv.eval(self.thy, goal).hyps) - set(init_As))
        self.add_line_before(id, 1+len(new_As))
        self.set_line(id, "sorry", th=Thm(cur_item.th.hyps, new_goal))
        for i, A in enumerate(new_As):
            self.set_line(incr_id(id, i+1), "sorry", th=Thm(cur_item.th.hyps, A))

        prev_ids = [incr_id(id, i) for i in range(1+len(new_As))]
        self.set_line(incr_id(id, 1+len(new_As)), "rewrite_goal", args=(th_name, goal), prevs=prev_ids)

        # Test if the goal is already proved
        new_id = self.find_goal(Thm(cur_item.th.hyps, new_goal), id)
        if new_id is not None:
            self.replace_id(id, new_id)
