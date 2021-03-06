# Author: Bohua Zhan

"""Utility functions for GCL (Guarded Command Language)."""

from kernel.type import TFun, TConst, BoolType, NatType
from kernel import term
from kernel.term import Term, Const, Eq, Binary
from logic import basic
from logic import logic
from data import function

thy = basic.load_theory("gcl")

varType = TConst("varType")
Ident = Const("Ident", TFun(NatType, varType))
Para = Const("Para", TFun(varType, NatType, varType))

scalarValue = TConst("scalarValue")
NatV = Const("NatV", TFun(NatType, scalarValue))
BoolV = Const("BoolV", TFun(BoolType, scalarValue))

stateT = TFun(varType, scalarValue)

def convert_term(var_map, s, t):
    """Convert term t with given var_map and state s.

    Examples: given var_map {a: 0, b: 1}, where a is a function
    and b is a scalar.

    convert_term(var_map, s, b) = s (Ident 1)
    convert_term(var_map, s, a(i)) = s (Para (Ident 0) i)
    convert_term(var_map, s, 2) = NatV 2
    convert_term(var_map, s, true) = BoolV true.

    """
    def convert(t):
        if t.head in var_map:
            if len(t.args) == 0:
                return s(Ident(Binary(var_map[t.head])))
            elif len(t.args) == 1:
                return s(Para(Ident(Binary(var_map[t.head])), t.arg))
            else:
                raise NotImplementedError
        elif t.is_equals():
            return Eq(convert(t.arg1), convert(t.arg))
        elif t.is_not():
            return term.Not(convert(t.arg))
        elif t.is_conj():
            return term.And(convert(t.arg1), convert(t.arg))
        elif t.is_disj():
            return term.Or(convert(t.arg1), convert(t.arg))
        elif t.get_type() == BoolType:
            return BoolV(t)
        elif t.get_type() == NatType:
            return NatV(t)
        else:
            raise NotImplementedError

    return convert(t)
    
def mk_assign(var_map, s, assigns):
    """Given a dictionary of assignments, form the corresponding term.

    Example: given var_map {a: 0, b: 1}, where a is a function
    and b is a scalar.

    mk_assign(var_map, s, {a(i): 2}) = (s)(Para (Ident 0) i := 2)
    mk_assign(var_map, s, {b: 1}) = (s)(Ident 1 := 1)

    """
    assign_args = []
    for k, v in assigns.items():
        k2 = convert_term(var_map, s, k)
        assert k2.fun == s, "mk_assign: key is not an identifer."
        assign_args.append(k2.arg)
        assign_args.append(convert_term(var_map, s, v))

    return function.mk_fun_upd(s, *assign_args)
