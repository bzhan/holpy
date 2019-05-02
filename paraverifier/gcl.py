# Author: Bohua Zhan

"""Utility functions for GCL (Guarded Command Language)."""

from kernel.type import TFun, Type, boolT
from kernel.term import Term, Const
from logic import basic
from logic.nat import natT, to_binary
from logic import logic
from logic import function

thy = basic.load_theory("gcl")

varType = Type("varType")
Ident = Const("Ident", TFun(natT, varType))
Para = Const("Para", TFun(varType, natT, varType))

scalarValue = Type("scalarValue")
NatV = Const("NatV", TFun(natT, scalarValue))
BoolV = Const("BoolV", TFun(boolT, scalarValue))

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
                return s(Ident(to_binary(var_map[t.head])))
            elif len(t.args) == 1:
                return s(Para(Ident(to_binary(var_map[t.head])), t.arg))
            else:
                raise NotImplementedError
        elif t.is_equals():
            return Term.mk_equals(convert(t.arg1), convert(t.arg))
        elif logic.is_neg(t):
            return logic.neg(convert(t.arg))
        elif logic.is_conj(t):
            return logic.conj(convert(t.arg1), convert(t.arg))
        elif logic.is_disj(t):
            return logic.disj(convert(t.arg1), convert(t.arg))
        elif t.get_type() == boolT:
            return BoolV(t)
        elif t.get_type() == natT:
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
