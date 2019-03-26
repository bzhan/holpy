# Author: Bohua Zhan

from kernel.type import Type, TFun, hol_bool
from kernel.term import Term, Const
from kernel.macro import MacroSig, global_macros
from logic import nat
from logic import function
from logic import logic
from logic.conv import arg_conv, then_conv, top_conv, beta_conv, binop_conv, \
    every_conv, rewr_conv, assums_conv
from logic.proofterm import ProofTerm, ProofTermMacro, ProofTermDeriv
from logic.logic_macro import init_theorem, apply_theorem
from prover import z3wrapper


"""Automation for Hoare logic."""

def comT(T):
    return Type("com", T)

def Skip(T):
    return Const("Skip", comT(T))

def Assign(Ta, Tb):
    return Const("Assign", TFun(Ta, TFun(TFun(Ta, Tb), Tb), comT(TFun(Ta, Tb))))

def Seq(T):
    return Const("Seq", TFun(comT(T), comT(T), comT(T)))

def Cond(T):
    return Const("Cond", TFun(TFun(T, hol_bool), comT(T), comT(T), comT(T)))

def While(T):
    return Const("While", TFun(TFun(T, hol_bool), TFun(T, hol_bool), comT(T), comT(T)))

def Sem(T):
    return Const("Sem", TFun(comT(T), T, T, hol_bool))

def Valid(T):
    return Const("Valid", TFun(TFun(T, hol_bool), comT(T), TFun(T, hol_bool), hol_bool))

def Entail(T):
    return Const("Entail", TFun(TFun(T, hol_bool), TFun(T, hol_bool), hol_bool))

# Normalize evaluation of function as well as arithmetic.
norm_cv = then_conv(top_conv(function.fun_upd_eval_conv()), nat.norm_full())

# Normalize a condition.
norm_cond_cv = every_conv(
    norm_cv,
    top_conv(nat.nat_eq_conv()),
    logic.norm_bool_expr()
)

class eval_Sem_macro(ProofTermMacro):
    """Prove a theorem of the form Sem com st st2."""
    def __init__(self):
        self.level = 10
        self.sig = MacroSig.TERM

    def eval_Sem(self, thy, com, st):
        """Evaluates the effect of program com on state st."""
        f, args = com.strip_comb()
        T = st.get_type()
        if f.is_const_with_name("Skip"):
            return init_theorem(thy, "Sem_Skip", tyinst={"a": T}, inst={"s": st})
        elif f.is_const_with_name("Assign"):
            a, b = args
            Ta = a.get_type()
            Tb = b.get_type().range_type()
            pt = init_theorem(thy, "Sem_Assign", tyinst={"a": Ta, "b": Tb}, inst={"a": a, "b": b, "s": st})
            return arg_conv(arg_conv(norm_cv)).apply_to_pt(thy, pt)
        elif f.is_const_with_name("Seq"):
            c1, c2 = args
            pt1 = self.eval_Sem(thy, c1, st)
            pt2 = self.eval_Sem(thy, c2, pt1.prop.arg)
            pt = apply_theorem(thy, "Sem_seq", pt1, pt2)
            return arg_conv(function.fun_upd_norm_one_conv()).apply_to_pt(thy, pt)
        elif f.is_const_with_name("Cond"):
            b, c1, c2 = args
            b_st = top_conv(beta_conv())(thy, b(st)).prop.arg
            b_eval = norm_cond_cv.get_proof_term(thy, b_st)
            if b_eval.prop.arg == logic.true:
                b_res = rewr_conv("eq_true", sym=True).apply_to_pt(thy, b_eval)
                pt1 = self.eval_Sem(thy, c1, st)
                return apply_theorem(thy, "Sem_if1", b_res, pt1, concl=Sem(T)(com, st, pt1.prop.arg))
            else:
                b_res = rewr_conv("eq_false", sym=True).apply_to_pt(thy, b_eval)
                pt2 = self.eval_Sem(thy, c2, st)
                return apply_theorem(thy, "Sem_if2", b_res, pt2, concl=Sem(T)(com, st, pt2.prop.arg))
        elif f.is_const_with_name("While"):
            b, inv, c = args
            b_st = top_conv(beta_conv())(thy, b(st)).prop.arg
            b_eval = norm_cond_cv.get_proof_term(thy, b_st)
            if b_eval.prop.arg == logic.true:
                b_res = rewr_conv("eq_true", sym=True).apply_to_pt(thy, b_eval)
                pt1 = self.eval_Sem(thy, c, st)
                pt2 = self.eval_Sem(thy, com, pt1.prop.arg)
                pt = apply_theorem(thy, "Sem_while_loop", b_res, pt1, pt2,
                                   concl=Sem(T)(com, st, pt2.prop.arg), inst={"s3": pt1.prop.arg})
                return arg_conv(function.fun_upd_norm_one_conv()).apply_to_pt(thy, pt)
            else:
                b_res = rewr_conv("eq_false", sym=True).apply_to_pt(thy, b_eval)
                return apply_theorem(thy, "Sem_while_skip", b_res, concl=Sem(T)(com, st, st))
        else:
            raise NotImplementedError

    def get_proof_term(self, thy, args, pts):
        assert len(pts) == 0, "eval_Sem_macro"
        f, (com, st, st2) = args.strip_comb()
        pt = self.eval_Sem(thy, com, st)
        assert st2 == pt.prop.arg, "eval_Sem_macro: wrong result."
        return pt


def compute_wp(thy, c, Q):
    """Compute the weakest precondition for the given command
    and postcondition. The computation is by case analysis on
    the form of c. Returns the validity theorem.

    """
    T = Q.get_type().domain_type()
    f, args = c.strip_comb()
    if f.is_const_with_name("Assign"):  # Assign a b
        a, b = args
        Ta, Tb = T.domain_type(), T.range_type()
        return init_theorem(thy, "assign_rule", tyinst={"a": Ta, "b": Tb},
                            inst={"a": a, "b": b, "P": Q})
    elif f.is_const_with_name("Seq"):  # Seq c1 c2
        wp1 = compute_wp(thy, args[1], Q)
        Q1 = wp1.prop.args[0]
        wp2 = compute_wp(thy, args[0], Q1)
        return apply_theorem(thy, "seq_rule", wp2, wp1)
    elif f.is_const_with_name("While"):  # While b I c
        pt = apply_theorem(thy, "while_rule", concl=Valid(T)(args[1], c, Q))
        pt0 = ProofTerm.assume(pt.assums[0])
        pt1 = vcg(thy, pt.assums[1])
        return ProofTerm.implies_elim(pt, pt0, pt1)
    else:
        raise NotImplementedError

def vcg(thy, goal):
    """Compute the verification conditions for the goal."""
    f, (P, c, Q) = goal.strip_comb()
    T = Q.get_type().domain_type()

    pt = compute_wp(thy, c, Q)
    entail_P = ProofTerm.assume(Entail(T)(P, pt.prop.args[0]))
    return apply_theorem(thy, "pre_rule", entail_P, pt)

class vcg_macro(ProofTermMacro):
    """Compute the verification conditions for a hoare triple, then
    normalizes the verification conditions.
    
    """
    def __init__(self):
        self.level = 10
        self.sig = MacroSig.TERM

    def get_proof_term(self, thy, goal, pts):
        pt = vcg(thy, goal)
        cv = every_conv(rewr_conv("Entail_def"), top_conv(beta_conv()),
                        top_conv(function.fun_upd_eval_conv()))
        for A in reversed(pt.hyps):
            pt = ProofTerm.implies_intr(A, pt)
        pt = assums_conv(cv).apply_to_pt(thy, pt)
        return pt

def vcg_solve(thy, goal):
    """Compute the verification conditions for a hoare triple, then
    solves the verification conditions using SMT.
    
    """
    pt = ProofTermDeriv("vcg", thy, goal, [])
    vc_pt = [ProofTermDeriv("z3", thy, vc, []) for vc in pt.assums]
    return ProofTerm.implies_elim(pt, *vc_pt)


global_macros.update({
    "eval_Sem": eval_Sem_macro(),
    "vcg": vcg_macro(),
})
