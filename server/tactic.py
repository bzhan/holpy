# Author: Bohua Zhan

from kernel import term
from kernel.term import Term
from kernel.thm import Thm
from logic import logic
from logic import matcher
from logic.conv import then_conv, top_conv, rewr_conv, beta_conv
from logic.proofterm import ProofTerm, ProofTermDeriv
from logic.logic_macro import apply_theorem
from syntax import printer

class Tactic:
    """Represents a tactic function.

    A tactic takes a proof term containing a single step with rule
    sorry, and converts it to a proof term containing zero or more
    sorries. Tactics can be combined in the usual manner.

    """
    def get_proof_term(self, thy, goal):
        raise NotImplementedError


class rule(Tactic):
    """Apply a theorem in the backward direction."""
    def __init__(self, th_name=None, prevs=None, instsp=None):
        assert th_name is None or isinstance(th_name, str), "rule: argument"
        self.th_name = th_name
        self.prevs = prevs if prevs else []
        self.instsp = instsp

    def search(self, thy, goal):
        results = []
        for name, th in thy.get_data("theorems").items():
            if 'hint_backward' not in thy.get_attributes(name):
                continue

            instsp = (dict(), dict())
            As, C = th.assums, th.concl
            # Only process those theorems where C and the matched As
            # contain all of the variables.
            if set(term.get_vars(As[:len(self.prevs)] + [C])) != set(term.get_vars(As + [C])):
                continue

            # When there is no assumptions to match, only process those
            # theorems where C contains at least a constant (skip falseE,
            # induction theorems, etc).
            if not self.prevs and term.get_consts(C) == []:
                continue

            try:
                for pat, prev in zip(As, self.prevs):
                    matcher.first_order_match_incr(pat, prev.prop, instsp)
                matcher.first_order_match_incr(C, goal.prop, instsp)
            except matcher.MatchException:
                continue

            # All matches succeed
            t = logic.subst_norm(th.prop, instsp)
            t = printer.print_term(thy, t)
            results.append((name, t))
        return sorted(results)

    def get_proof_term(self, thy, goal):
        if isinstance(self.th_name, str):
            th = thy.get_theorem(self.th_name)

        As, C = th.assums, th.concl

        if self.instsp is None:
            instsp = (dict(), dict())
            matcher.first_order_match_incr(C, goal.prop, instsp)
            for pat, prev in zip(As, self.prevs):
                matcher.first_order_match_incr(pat, prev.prop, instsp)
        else:
            instsp = self.instsp

        As, _ = logic.subst_norm(th.prop, instsp).strip_implies()
        pts = self.prevs + [ProofTerm.sorry(Thm(goal.hyps, A)) for A in As[len(self.prevs):]]

        if set(term.get_vars(th.assums)) != set(term.get_vars(th.prop)):
            tyinst, inst = instsp
            return apply_theorem(thy, self.th_name, *pts, tyinst=tyinst, inst=inst)
        else:
            return apply_theorem(thy, self.th_name, *pts)

class intros(Tactic):
    """Given a goal of form !x_1 ... x_n. A_1 --> ... --> A_n --> C,
    introduce variables for x_1, ..., x_n and assumptions for A_1, ..., A_n.
    
    """
    def __init__(self, *var_names):
        self.var_names = var_names

    def get_proof_term(self, thy, goal):
        vars, As, C = logic.strip_all_implies(goal.prop, self.var_names)
        
        pt = ProofTerm.sorry(Thm(list(goal.hyps) + As, C))
        ptAs = [ProofTerm.assume(A) for A in As]
        ptVars = [ProofTerm.variable(var.name, var.T) for var in vars]
        return ProofTermDeriv('intros', thy, None, ptVars + ptAs + [pt])

class var_induct(Tactic):
    """Apply induction rule on a variable."""
    def __init__(self, th_name, var):
        self.th_name = th_name
        self.var = var

    def get_proof_term(self, thy, goal):
        P = Term.mk_abs(self.var, goal.prop)
        th = thy.get_theorem(self.th_name)
        f, args = th.concl.strip_comb()
        if len(args) != 1:
            raise NotImplementedError
        inst = {f.name: P, args[0].name: self.var}
        return rule(self.th_name, instsp=({}, inst)).get_proof_term(thy, goal)

class rewrite(Tactic):
    """Rewrite the goal using a theorem."""
    def __init__(self, th_name=None):
        assert th_name is None or isinstance(th_name, str), "rule: argument"
        self.th_name = th_name

    def search(self, thy, goal):
        results = []
        for th_name, th in thy.get_data("theorems").items():
            if 'hint_rewrite' not in thy.get_attributes(th_name):
                continue

            cv = top_conv(rewr_conv(th_name))
            new_goal = cv.eval(thy, goal.prop).prop.rhs
            if goal.prop != new_goal:
                new_goal = printer.print_term(thy, new_goal)
                results.append((th_name, new_goal))

        return sorted(results)

    def get_proof_term(self, thy, goal):
        init_As = goal.hyps
        C = goal.prop
        cv = then_conv(top_conv(rewr_conv(self.th_name)),
                       top_conv(beta_conv()))
        new_goal = cv.eval(thy, C).prop.rhs
        new_goal_pts = ProofTerm.sorry(Thm(init_As, new_goal))

        new_As = list(set(cv.eval(thy, C).hyps) - set(init_As))
        new_As_pts = [ProofTerm.sorry(Thm(init_As, A)) for A in new_As]
        return ProofTermDeriv('rewrite_goal', thy, args=(self.th_name, C), prevs=[new_goal_pts] + new_As_pts)
