# Author: Bohua Zhan

from kernel.type import TFun
from kernel.term import Term, Const, Abs
from kernel.macro import MacroSig, global_macros
from logic import logic_macro
from logic import nat
from logic import logic
from logic.conv import Conv, rewr_conv_thm
from logic.proofterm import ProofTerm, ProofTermDeriv, ProofTermMacro

"""Utility functions for the function library."""

def is_fun_upd(t):
    """Whether t is fun_upd applied to three parameters, that
    is, whether t is of the form f (a := b).

    """
    c, args = t.strip_comb()
    return len(args) == 3 and c.is_const_with_name("fun_upd")

def fun_upd(T1, T2):
    """Returns the term fun_upd on functions of type T1 => T2."""
    return Const("fun_upd", TFun(TFun(T1, T2), T1, T2, T1, T2))

def mk_const_fun(T, k):
    """Returns the term %x::T. k."""
    return Abs("x", T, k)

def mk_fun_upd(*args):
    """Returns the term (f)(a1 := b1, a2 := b2, ...)."""
    if len(args) == 3:
        f, a, b = args
        return fun_upd(a.get_type(), b.get_type())(f, a, b)
    elif len(args) > 3:
        return mk_fun_upd(mk_fun_upd(*args[:3]), *args[3:])
    else:
        raise TypeError()

def strip_fun_upd(t):
    """Given t of the form (f)(a1 := b1, a2 := b2, ...), return
    (f, [(a1, b1), (a2, b2), ...]).

    """
    if is_fun_upd(t):
        _, (f1, a, b) = t.strip_comb()
        f, upds = strip_fun_upd(f1)
        return f, upds + [(a, b)]
    else:
        return t, []

class fun_upd_conv(Conv):
    """Evaluate the function (f)(a1 := b1, a2 := b2, ...) on an input."""

    def get_proof_term(self, t):
        from logic import basic
        thy = basic.loadTheory('function')

        f, c = t.fun, t.arg
        if is_fun_upd(f):
            _, (f1, a, b) = f.strip_comb()
            if a == c:
                return rewr_conv_thm(thy, "fun_upd_same").get_proof_term(t)
            else:
                pt = logic_macro.init_theorem(
                    thy, "fun_upd_other",
                    tyinst={"a": nat.natT, "b": nat.natT},
                    inst={"f": f1, "a": a, "b": b, "c": c})
                macro = nat.nat_const_ineq_macro()
                goal = logic.neg(Term.mk_equals(c, a))
                cond = ProofTermDeriv(macro(thy, goal), "nat_const_ineq", goal, [])
                eq = ProofTerm.implies_elim(pt, cond)

                eq2 = self.get_proof_term(eq.th.concl.arg)
                return ProofTerm.transitive(eq, eq2)
        else:
            return ProofTerm.beta_conv(t)

class fun_upd_eval_macro(ProofTermMacro):
    """Macro using fun_upd_conv."""

    def __init__(self):
        self.level = 10
        self.sig = MacroSig.TERM
        self.has_theory = False
        self.use_goal = True

    def __call__(self, args):
        # Simply produce the goal
        return Thm([], args)

    def get_proof_term(self, args):
        assert args.is_equals(), "fun_upd_eval_macro: goal is not an equality"

        t1, t2 = args.arg1, args.arg
        pt = fun_upd_conv().get_proof_term(t1)
        assert pt.th.concl.arg == t2, "fun_upd_eval_macro: incorrect rhs"

        return pt

global_macros.update({
    "fun_upd_eval": fun_upd_eval_macro(),
})
