# Author: Bohua Zhan

from kernel.type import TFun
from kernel.term import Term, Const, Abs
from kernel.macro import MacroSig, global_macros
from logic import logic_macro
from logic import nat
from logic import logic
from logic.conv import Conv, rewr_conv, then_conv, arg_conv, argn_conv
from logic.proofterm import ProofTerm, ProofTermMacro, refl

"""Utility functions for the function library."""

def is_fun_upd(t):
    """Whether t is fun_upd applied to three parameters, that
    is, whether t is of the form f (a := b).

    """
    c, args = t.strip_comb()
    return len(args) == 3 and c.is_const_name("fun_upd")

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
        f1, a, b = t.args
        f, upds = strip_fun_upd(f1)
        return f, upds + [(a, b)]
    else:
        return t, []

class fun_upd_eval_conv(Conv):
    """Evaluate the function (f)(a1 := b1, a2 := b2, ...) on an input."""

    def get_proof_term(self, thy, t):
        if t.ty != Term.COMB:
            return refl(t)

        f, c = t.fun, t.arg
        if is_fun_upd(f):
            f1, a, b = f.args
            if a == c:
                return rewr_conv("fun_upd_same").get_proof_term(thy, t)
            else:
                neq = nat.nat_const_ineq(thy, c, a)
                eq = rewr_conv("fun_upd_other", conds=[neq]).get_proof_term(thy, t)
                return eq.on_arg(thy, self)
        elif f.ty == Term.ABS:
            return ProofTerm.beta_conv(t)
        else:
            return refl(t)

class fun_upd_eval_macro(ProofTermMacro):
    """Macro using fun_upd_eval_conv."""

    def __init__(self):
        self.level = 10
        self.sig = MacroSig.TERM

    def get_proof_term(self, thy, args, pts):
        assert len(pts) == 0, "fun_upd_eval_macro"
        assert args.is_equals(), "fun_upd_eval_macro: goal is not an equality"

        t1, t2 = args.arg1, args.arg
        pt = fun_upd_eval_conv().get_proof_term(t1)
        assert pt.prop.arg == t2, "fun_upd_eval_macro: incorrect rhs"

        return pt

class fun_upd_norm_one_conv(Conv):
    """Normalize a function update (f)(a1 := b1, ...)(an := bn) by moving
    the last update to the right position, combining if necessary.

    """
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_fun_upd(t) and is_fun_upd(t.args[0]):
            f, a, b = t.args
            f2, a2, b2 = f.args
            if nat.from_binary(a) < nat.from_binary(a2):
                neq = nat.nat_const_ineq(thy, a, a2)
                return pt.on_rhs(thy, rewr_conv("fun_upd_twist", conds=[neq]), argn_conv(0, self))
            elif nat.from_binary(a) == nat.from_binary(a2):
                return pt.on_rhs(thy, rewr_conv("fun_upd_upd"))
            else:
                return pt
        else:
            return pt

class fun_upd_norm_conv(Conv):
    """Normalize a function update of the form (f)(a1 := b1, a2 := b2, ...).

    This sorts the updates according to the key (provided in the constructor),
    and combines updates on the same key.

    """
    def get_proof_term(self, thy, t):
        pt = refl(t)
        if is_fun_upd(t):
            return pt.on_rhs(thy, argn_conv(0, self), fun_upd_norm_one_conv())
        else:
            return pt


global_macros.update({
    "fun_upd_eval": fun_upd_eval_macro(),
})
