# Author: Bohua Zhan

from copy import copy

from kernel.type import TyInst
from kernel import term
from kernel.term import Term, Implies, Not, Lambda, Inst
from kernel.thm import Thm
from kernel import theory
from kernel.proofterm import ProofTerm, TacticException
from logic import logic
from logic import matcher
from logic.conv import then_conv, top_conv, rewr_conv, beta_conv, beta_norm_conv, \
    top_sweep_conv, has_rewrite
from logic.logic import apply_theorem


class Tactic:
    """Represents a tactic function.

    A tactic takes a target theorem, and returns a proof term
    containing zero or more sorries. Tactics can be combined in the
    usual manner.

    get_proof_term can be supplied with two more arguments: args
    for extra data provided to the tactic, and prevs for the list
    of existing facts to use.

    """
    def get_proof_term(self, goal, *, args=None, prevs=None) -> ProofTerm:
        raise NotImplementedError


class MacroTactic(Tactic):
    """Construct a tactic from a macro.
    
    The name of the macro is provided at initialization. The first
    argument of the macro must be the goal statement. The remaining
    arguments are supplied by the tactic.
    
    """
    def __init__(self, macro):
        self.macro = macro

    def get_proof_term(self, goal, *, args=None, prevs=None):
        assert isinstance(goal, Thm), "MacroTactic"
        if prevs is None:
            prevs = []

        if args is None:
            args = goal.prop
        else:
            args = (goal.prop,) + args

        return ProofTerm(self.macro, args, prevs)

class rule(Tactic):
    """Apply a theorem in the backward direction.
    
    args is either a pair of theorem name and instantiation, or the
    theorem name alone.

    """
    def get_proof_term(self, goal, *, args=None, prevs=None):
        if isinstance(args, tuple):
            th_name, inst = args
        else:
            th_name, inst = args, None
        assert isinstance(th_name, str), "rule: theorem name must be a string"

        if prevs is None:
            prevs = []
        
        th = theory.get_theorem(th_name)
        As, C = th.assums, th.concl

        # Length of prevs is at most length of As
        assert len(prevs) <= len(As), "rule: too many previous facts"
        if inst is None:
            inst = Inst()

        # Match the conclusion and assumptions. Either the conclusion
        # or the list of assumptions must be a first-order pattern.
        if matcher.is_pattern(C, []):
            inst = matcher.first_order_match(C, goal.prop, inst)
            for pat, prev in zip(As, prevs):
                inst = matcher.first_order_match(pat, prev.prop, inst)
        else:
            for pat, prev in zip(As, prevs):
                inst = matcher.first_order_match(pat, prev.prop, inst)
            inst = matcher.first_order_match(C, goal.prop, inst)

        # Check that every variable in the theorem has an instantiation.
        unmatched_vars = [v.name for v in term.get_svars(As + [C]) if v.name not in inst]
        if unmatched_vars:
            raise theory.ParameterQueryException(list("param_" + name for name in unmatched_vars))

        # Substitute and normalize
        As, _ = th.prop.subst_norm(inst).strip_implies()
        goal_Alen = len(goal.assums)
        if goal_Alen > 0:
            As = As[:-goal_Alen]

        pts = prevs + [ProofTerm.sorry(Thm(A, goal.hyps)) for A in As[len(prevs):]]

        # Determine whether it is necessary to provide instantiation
        # to apply_theorem.
        if set(term.get_svars(th.assums)) != set(th.prop.get_svars()) or \
           set(term.get_stvars(th.assums)) != set(th.prop.get_stvars()) or \
           not matcher.is_pattern_list(th.assums, []):
            return apply_theorem(th_name, *pts, inst=inst)
        else:
            return apply_theorem(th_name, *pts)

class resolve(Tactic):
    """Given any goal, a theorem of the form ~A, and an existing fact A,
    solve the goal.
    
    """
    def get_proof_term(self, goal, args, prevs):
        assert isinstance(args, str) and len(prevs) == 1, "resolve: type"
        th_name = args
        th = theory.get_theorem(th_name)

        assert th.prop.is_not(), "resolve: prop is not a negation"

        # Checking that the theorem matches the fact is done here.
        return ProofTerm('resolve_theorem', (args, goal.prop), prevs)

class intros(Tactic):
    """Given a goal of form !x_1 ... x_n. A_1 --> ... --> A_n --> C,
    introduce variables for x_1, ..., x_n and assumptions for A_1, ..., A_n.
    
    """
    def get_proof_term(self, goal, *, args=None, prevs=None):
        if args is None:
            var_names = []
        else:
            var_names = args

        vars, As, C = logic.strip_all_implies(goal.prop, var_names, svar=False)
        
        pt = ProofTerm.sorry(Thm(C, goal.hyps, tuple(As)))
        ptAs = [ProofTerm.assume(A) for A in As]
        ptVars = [ProofTerm.variable(var.name, var.T) for var in vars]
        return ProofTerm('intros', None, ptVars + ptAs + [pt])

class var_induct(Tactic):
    """Apply induction rule on a variable."""
    def get_proof_term(self, goal, *, args=None, prevs=None):
        th_name, var = args
        P = Lambda(var, goal.prop)
        th = theory.get_theorem(th_name)
        f, th_args = th.concl.strip_comb()
        if len(th_args) != 1:
            raise NotImplementedError
        inst = matcher.first_order_match(th_args[0], var)
        inst[f.name] = P
        As, _ = th.prop.subst_norm(inst).strip_implies()
        pts = [ProofTerm.sorry(Thm(A, goal.hyps)) for A in As]
        return ProofTerm("apply_induct", (th_name, var, goal.prop), pts)

class rewrite_goal(Tactic):
    """Rewrite the goal using a theorem."""
    def __init__(self, *, sym=False):
        self.sym = sym

    def get_proof_term(self, goal, *, args=None, prevs=None):
        th_name = args
        C = goal.prop

        # Check whether rewriting using the theorem has an effect
        assert has_rewrite(th_name, C, sym=self.sym, conds=prevs), \
            "rewrite: unable to apply theorem."

        cv = then_conv(top_sweep_conv(rewr_conv(th_name, sym=self.sym, conds=prevs)),
                       beta_norm_conv())
        eq_th = cv.eval(C)
        new_goal = eq_th.prop.rhs

        if self.sym:
            macro_name = 'rewrite_goal_sym'
        else:
            macro_name = 'rewrite_goal'
        if new_goal.is_equals() and new_goal.lhs == new_goal.rhs:
            return ProofTerm(macro_name, args=(th_name, C), prevs=prevs)
        else:
            new_goal = ProofTerm.sorry(Thm(new_goal, goal.hyps))
            assert new_goal.prop != goal.prop, "rewrite: unable to apply theorem"
            return ProofTerm(macro_name, args=(th_name, C), prevs=[new_goal] + prevs)

class rewrite_goal_with_prev(Tactic):
    def get_proof_term(self, goal, *, args=None, prevs=None):
        assert isinstance(prevs, list) and len(prevs) == 1, "rewrite_goal_with_prev"
        pt = prevs[0]
        C = goal.prop

        # In general, we assume pt.th has forall quantification.
        # First, obtain the patterns
        new_names = logic.get_forall_names(pt.prop)
        new_vars, prev_As, prev_C = logic.strip_all_implies(pt.prop, new_names)

        # Fact used must be an equality
        assert len(prev_As) == 0 and prev_C.is_equals(), "rewrite_goal_with_prev"

        for new_var in new_vars:
            pt = pt.forall_elim(new_var)

        # Check whether rewriting using the theorem has an effect
        assert has_rewrite(pt.th, C), "rewrite_goal_with_prev"

        cv = then_conv(top_sweep_conv(rewr_conv(pt)),
                       beta_norm_conv())
        eq_th = cv.eval(C)
        new_goal = eq_th.prop.rhs

        prevs = list(prevs)
        if not new_goal.is_reflexive():
            prevs.append(ProofTerm.sorry(Thm(new_goal, goal.hyps)))
        return ProofTerm('rewrite_goal_with_prev', args=C, prevs=prevs)

class apply_prev(Tactic):
    """Applies an existing fact in the backward direction."""
    def get_proof_term(self, goal, *, args=None, prevs=None):
        assert isinstance(prevs, list) and len(prevs) >= 1, "apply_prev"
        pt, prev_pts = prevs[0], prevs[1:]

        # First, obtain the patterns
        new_names = logic.get_forall_names(pt.prop)
        new_vars, As, C = logic.strip_all_implies(pt.prop, new_names)
        assert len(prev_pts) <= len(As), "apply_prev: too many prev_pts"

        if args is None:
            inst = Inst()
        else:
            inst = args
        inst = matcher.first_order_match(C, goal.prop, inst)
        for idx, prev_pt in enumerate(prev_pts):
            inst = matcher.first_order_match(As[idx], prev_pt.prop, inst)

        unmatched_vars = [v for v in new_names if v not in inst]
        if unmatched_vars:
            raise theory.ParameterQueryException(list("param_" + name for name in unmatched_vars))

        pt = pt.subst_type(inst.tyinst)
        for new_name in new_names:
            pt = pt.forall_elim(inst[new_name])
        if pt.prop.beta_norm() != pt.prop:
            pt = pt.on_prop(beta_norm_conv())
        inst_As, inst_C = pt.prop.strip_implies()

        inst_arg = [inst[new_name] for new_name in new_names]
        new_goals = [ProofTerm.sorry(Thm(A, goal.hyps)) for A in inst_As[len(prev_pts):]]
        if set(new_names).issubset({v.name for v in term.get_vars(As)}) and \
           matcher.is_pattern_list(As, []):
            return ProofTerm('apply_fact', args=None, prevs=prevs + new_goals)
        else:
            return ProofTerm('apply_fact_for', args=inst_arg, prevs=prevs + new_goals)

class cases(Tactic):
    """Case checking on an expression."""
    def get_proof_term(self, goal, *, args=None, prevs=None):
        assert isinstance(args, Term), "cases"

        As = goal.hyps
        C = goal.prop
        goal1 = ProofTerm.sorry(Thm(Implies(args, C), goal.hyps))
        goal2 = ProofTerm.sorry(Thm(Implies(Not(args), C), goal.hyps))
        return apply_theorem('classical_cases', goal1, goal2)

class inst_exists_goal(Tactic):
    """Instantiate an exists goal."""
    def get_proof_term(self, goal, *, args=None, prevs=None):
        assert isinstance(args, Term), "inst_exists_goal"

        C = goal.prop
        assert C.is_exists(), "inst_exists_goal: goal is not exists statement"
        argT = args.get_type()
        assert C.arg.var_T == argT, "inst_exists_goal: incorrect type: expect %s, given %s" % (
            str(C.arg.var_T), str(argT)
        )

        return rule().get_proof_term(goal, args=('exI', Inst(P=C.arg, a=args)))


class intro_imp_tac(Tactic):
    def get_proof_term(self, goal):
        if not goal.prop.is_implies():
            raise TacticException('intro_imp: goal is not implies.')

        A, C = goal.prop.args
        new_goal = ProofTerm.sorry(Thm(C, goal.hyps, A))
        return new_goal.implies_intr(A)

class intro_forall_tac(Tactic):
    def __init__(self, var_name=None):
        self.var_name = var_name
        
    def get_proof_term(self, goal):
        if not goal.prop.is_forall():
            raise TacticException('intro_forall: goal is not forall')

        v, body = goal.prop.arg.dest_abs(self.var_name)
        new_goal = ProofTerm.sorry(Thm(body, goal.hyps))
        return new_goal.forall_intr(v)

class assumption(Tactic):
    def get_proof_term(self, goal):
        if not goal.prop in goal.hyps:
            raise TacticException('assumption: prop does not appear in hyps')
        
        return ProofTerm.assume(goal.prop)

class then_tac(Tactic):
    def __init__(self, tac1, tac2):
        self.tac1 = tac1
        self.tac2 = tac2
        
    def get_proof_term(self, goal):
        return ProofTerm.sorry(goal).tacs(self.tac1, self.tac2)

class else_tac(Tactic):
    def __init__(self, tac1, tac2):
        self.tac1 = tac1
        self.tac2 = tac2
        
    def get_proof_term(self, goal):
        try:
            return self.tac1.get_proof_term(goal)
        except TacticException:
            return self.tac2.get_proof_term(goal)

class repeat_tac(Tactic):
    def __init__(self, tac):
        self.tac = tac
        
    def get_proof_term(self, goal):
        pt = ProofTerm.sorry(goal)
        while True:
            try:
                pt = pt.tac(self.tac)
            except TacticException:
                break
        return pt

intros_tac = repeat_tac(else_tac(intro_imp_tac(), intro_forall_tac()))

class rule_tac(Tactic):
    def __init__(self, th_name, *, inst=None):
        self.th_name = th_name
        if inst is None:
            inst = Inst()
        self.inst = inst
        
    def get_proof_term(self, goal):
        th = theory.get_theorem(self.th_name)
        try:
            inst = matcher.first_order_match(th.concl, goal.prop, self.inst)
        except matcher.MatchException:
            raise TacticException('rule: matching failed')
            
        if any(v.name not in inst for v in th.prop.get_svars()):
            raise TacticException('rule: not all variables are matched')
            
        pt = ProofTerm.theorem(self.th_name).substitution(inst).on_prop(beta_norm_conv())
        for assum in pt.assums:
            pt = pt.implies_elim(ProofTerm.sorry(Thm(assum, goal.hyps)))
        return pt


class elim_tac(Tactic):
    def __init__(self, th_name, *, cond=None, inst=None):
        self.th_name = th_name
        if inst is None:
            inst = Inst()
        self.inst = inst
        self.cond = cond
        
    def get_proof_term(self, goal):
        th = theory.get_theorem(self.th_name)

        assum = th.assums[0]
        cond = self.cond
        if cond is None:
            # Find cond by matching with goal.hyps one by one
            for hyp in goal.hyps:
                try:
                    inst = matcher.first_order_match(th.assums[0], hyp, self.inst)
                    cond = hyp
                    break
                except matcher.MatchException:
                    pass
        
        if cond is None:
            raise TacticException('elim: cannot match assumption')

        try:
            inst = matcher.first_order_match(th.concl, goal.prop, inst)
        except matcher.MatchException:
            raise TacticException('elim: matching failed')

        if any(v.name not in inst for v in th.prop.get_svars()):
            raise TacticException('elim: not all variables are matched')
            
        pt = ProofTerm.theorem(self.th_name).substitution(inst).on_prop(beta_norm_conv())
        pt = pt.implies_elim(ProofTerm.assume(cond))
        for assum in pt.assums:
            pt = pt.implies_elim(ProofTerm.sorry(Thm(assum, goal.hyps)))
        return pt


class conj_elim_tac(Tactic):
    def get_proof_term(self, goal):
        return ProofTerm.sorry(goal).tacs(
            elim_tac('conjE'), intro_imp_tac(), intro_imp_tac())
