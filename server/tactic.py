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

    A tactic takes a target theorem, and returns a proof term
    containing zero or more sorries. Tactics can be combined in the
    usual manner.

    get_proof_term can be supplied with two more arguments: args
    for extra data provided to the tactic, and prevs for the list
    of existing facts to use.

    """
    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        raise NotImplementedError


class rule(Tactic):
    """Apply a theorem in the backward direction."""
    def search(self, thy, goal, *, prevs=None):
        if prevs is None:
            prevs = []

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
            if not prevs and term.get_consts(C) == []:
                continue

            try:
                if matcher.is_pattern(C, []):
                    matcher.first_order_match_incr(C, goal.prop, instsp)
                    for pat, prev in zip(As, prevs):
                        matcher.first_order_match_incr(pat, prev.prop, instsp)
                else:
                    for pat, prev in zip(As, prevs):
                        matcher.first_order_match_incr(pat, prev.prop, instsp)
                    matcher.first_order_match_incr(C, goal.prop, instsp)
            except matcher.MatchException:
                continue

            # All matches succeed
            t = logic.subst_norm(th.prop, instsp)
            t = printer.print_term(thy, t)
            results.append((name, t))
        return sorted(results)

    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        if isinstance(args, tuple):
            th_name, instsp = args
        else:
            th_name = args
            instsp = None
        assert isinstance(th_name, str), "rule: theorem name must be a string"

        if prevs is None:
            prevs = []
        
        th = thy.get_theorem(th_name)
        As, C = th.assums, th.concl

        if instsp is None:
            instsp = (dict(), dict())
            if matcher.is_pattern(C, []):
                matcher.first_order_match_incr(C, goal.prop, instsp)
                for pat, prev in zip(As, prevs):
                    matcher.first_order_match_incr(pat, prev.prop, instsp)
            else:
                for pat, prev in zip(As, prevs):
                    matcher.first_order_match_incr(pat, prev.prop, instsp)
                matcher.first_order_match_incr(C, goal.prop, instsp)

        As, _ = logic.subst_norm(th.prop, instsp).strip_implies()
        pts = prevs + [ProofTerm.sorry(Thm(goal.hyps, A)) for A in As[len(prevs):]]

        if set(term.get_vars(th.assums)) != set(term.get_vars(th.prop)) or \
           not matcher.is_pattern_list(th.assums, []):
            tyinst, inst = instsp
            return apply_theorem(thy, th_name, *pts, tyinst=tyinst, inst=inst)
        else:
            return apply_theorem(thy, th_name, *pts)

class intros(Tactic):
    """Given a goal of form !x_1 ... x_n. A_1 --> ... --> A_n --> C,
    introduce variables for x_1, ..., x_n and assumptions for A_1, ..., A_n.
    
    """
    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        if args is None:
            var_names = []
        else:
            var_names = args

        vars, As, C = logic.strip_all_implies(goal.prop, var_names)
        
        pt = ProofTerm.sorry(Thm(list(goal.hyps) + As, C))
        ptAs = [ProofTerm.assume(A) for A in As]
        ptVars = [ProofTerm.variable(var.name, var.T) for var in vars]
        return ProofTermDeriv('intros', thy, None, ptVars + ptAs + [pt])

class var_induct(Tactic):
    """Apply induction rule on a variable."""
    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        th_name, var = args
        P = Term.mk_abs(var, goal.prop)
        th = thy.get_theorem(th_name)
        f, args = th.concl.strip_comb()
        if len(args) != 1:
            raise NotImplementedError
        inst = {f.name: P, args[0].name: var}
        return rule().get_proof_term(thy, goal, args=(th_name, ({}, inst)))

class rewrite(Tactic):
    """Rewrite the goal using a theorem."""
    def search(self, thy, goal, *, prevs=None):
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

    def get_proof_term(self, thy, goal, args=None, prevs=None):
        th_name = args

        init_As = goal.hyps
        C = goal.prop
        cv = then_conv(top_conv(rewr_conv(th_name)),
                       top_conv(beta_conv()))
        new_goal = cv.eval(thy, C).prop.rhs

        new_As = list(set(cv.eval(thy, C).hyps) - set(init_As))
        new_As_pts = [ProofTerm.sorry(Thm(init_As, A)) for A in new_As]
        if Term.is_equals(new_goal) and new_goal.lhs == new_goal.rhs:
            return ProofTermDeriv('rewrite_goal', thy, args=(th_name, C), prevs=new_As_pts)
        else:
            new_goal_pts = ProofTerm.sorry(Thm(init_As, new_goal))
            return ProofTermDeriv('rewrite_goal', thy, args=(th_name, C), prevs=[new_goal_pts] + new_As_pts)

class rewrite_goal_with_prev(Tactic):
    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        assert isinstance(prevs, list) and len(prevs) == 1, "rewrite_goal_with_prev"
        pt = prevs[0]

        init_As = goal.hyps
        C = goal.prop
        cv = then_conv(top_conv(rewr_conv(pt, match_vars=False)),
                       top_conv(beta_conv()))
        new_goal = cv.eval(thy, C).prop.rhs

        new_As = list(set(cv.eval(thy, C).hyps) - set(init_As))
        new_As_pts = [ProofTerm.sorry(Thm(init_As, A)) for A in new_As]
        if Term.is_equals(new_goal) and new_goal.lhs == new_goal.rhs:
            return ProofTermDeriv('rewrite_goal_with_prev', thy, args=C, prevs=[pt] + new_As_pts)
        else:
            new_goal_pts = ProofTerm.sorry(Thm(init_As, new_goal))
            return ProofTermDeriv('rewrite_goal_with_prev', thy, args=C, prevs=[pt, new_goal_pts] + new_As_pts)

class apply_prev(Tactic):
    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        assert isinstance(prevs, list) and len(prevs) == 1, "apply_prev"
        pt = prevs[0]

        assert pt.concl == goal.prop, "apply_prev"
        As_pts = [ProofTerm.sorry(Thm(goal.hyps, A)) for A in pt.assums]
        return ProofTerm.implies_elim(pt, *As_pts)

class cases(Tactic):
    """Case checking on an expression."""
    def get_proof_term(self, thy, goal, *, args=None, prevs=None):
        assert isinstance(args, Term), "cases"

        As = goal.hyps
        C = goal.prop
        goal1 = ProofTerm.sorry(Thm(goal.hyps, Term.mk_implies(args, C)))
        goal2 = ProofTerm.sorry(Thm(goal.hyps, Term.mk_implies(logic.neg(args), C)))
        return apply_theorem(thy, 'classical_cases', goal1, goal2)
