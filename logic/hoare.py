# Author: Bohua Zhan

from kernel.type import Type, TFun, hol_bool
from kernel.term import Term, Const
from kernel.macro import MacroSig, global_macros
from logic import nat
from logic import function
from logic import logic
from logic.conv import arg_conv, then_conv, top_conv, beta_conv, binop_conv, \
    every_conv, rewr_conv_thm_sym
from logic.proofterm import ProofTerm, ProofTermMacro
from logic.logic_macro import init_theorem, apply_theorem


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

def Sem(T):
    return Const("Sem", TFun(comT(T), T, T, hol_bool))

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
        self.has_theory = True
        self.use_goal = True

    def eval_cond(self, thy, b):
        if Term.is_equals(b):
            pt = binop_conv(self.norm_cv).get_proof_term(b)
            b2 = pt.th.concl.arg
            lhs, rhs = b2.arg1, b2.arg
            assert nat.is_binary(lhs) and nat.is_binary(rhs), \
                   "eval_Sem: cannot simplify to integer."
            if lhs == rhs:
                pt = ProofTerm.symmetric(pt)
                return True, ProofTerm.equal_elim(pt, ProofTerm.reflexive(lhs))
            else:
                pt = ProofTerm.combination(ProofTerm.reflexive(logic.neg), ProofTerm.symmetric(pt))
                return False, ProofTerm.equal_elim(pt, nat.nat_const_ineq(thy, lhs, rhs))
        else:
            raise NotImplementedError

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
            pt2 = arg_conv(arg_conv(norm_cv)).get_proof_term(pt.th.concl)
            return ProofTerm.equal_elim(pt2, pt)
        elif f.is_const_with_name("Seq"):
            c1, c2 = args
            pt1 = self.eval_Sem(thy, c1, st)
            st2 = pt1.th.concl.arg
            pt2 = self.eval_Sem(thy, c2, st2)
            pt = apply_theorem(thy, "Sem_seq", pt1, pt2)
            cv = function.fun_upd_norm_one_conv()
            pt2 = arg_conv(cv).get_proof_term(pt.th.concl)
            return ProofTerm.equal_elim(pt2, pt)
        elif f.is_const_with_name("Cond"):
            b, c1, c2 = args
            b_st = top_conv(beta_conv())(b(st)).concl.arg
            b_eval = norm_cond_cv.get_proof_term(b_st)
            if b_eval.th.concl.arg == logic.true:
                b_eq = rewr_conv_thm_sym(thy, "eq_True").get_proof_term(b_eval.th.concl)
                b_res = ProofTerm.equal_elim(b_eq, b_eval)
                pt1 = self.eval_Sem(thy, c1, st)
                st2 = pt1.th.concl.arg
                pt = init_theorem(thy, "Sem_if1", tyinst={"a": T}, inst={"b": b, "c1": c1, "c2": c2, "s": st, "s2": st2})
                return ProofTerm.implies_elim(ProofTerm.implies_elim(pt, b_res), pt1)
            else:
                b_eq = rewr_conv_thm_sym(thy, "eq_False").get_proof_term(b_eval.th.concl)
                b_res = ProofTerm.equal_elim(b_eq, b_eval)
                pt2 = self.eval_Sem(thy, c2, st)
                st2 = pt2.th.concl.arg
                pt = init_theorem(thy, "Sem_if2", tyinst={"a": T}, inst={"b": b, "c1": c1, "c2": c2, "s": st, "s2": st2})
                return ProofTerm.implies_elim(ProofTerm.implies_elim(pt, b_res), pt2)
        else:
            raise NotImplementedError

    def get_proof_term(self, thy, args, *pts):
        assert len(pts) == 0, "eval_Sem_macro"
        f, args = args.strip_comb()
        com, st, st2 = args
        pt = self.eval_Sem(thy, com, st)
        res_st2 = pt.th.concl.arg
        if st2 != res_st2:
            from syntax import printer
            print(printer.print_term(thy, st2))
            print(printer.print_term(thy, res_st2))
        assert st2 == res_st2, "eval_Sem_macro: wrong result."
        return pt

global_macros.update({
    "eval_Sem": eval_Sem_macro(),
})
