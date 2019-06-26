# Author: Bohua Zhan

import unittest

from kernel.type import TFun, boolT
from kernel.term import Var, Term
from logic import basic
from data.nat import natT, to_binary, zero, one
from logic import logic
from data import function
from paraverifier import gcl
from paraverifier.gcl import Para, Ident, NatV, BoolV
from syntax import printer

thy = basic.load_theory("gcl")
eq = Term.mk_equals

class GCLTest(unittest.TestCase):
    def testConvertTerm(self):
        a, b = Var("a", TFun(natT, natT)), Var("b", boolT)
        var_map = {a: 0, b: 1}
        s = Var("s", gcl.stateT)
        test_data = [
            (a(one), s(Para(Ident(zero), one))),
            (b, s(Ident(one))),
            (to_binary(3), NatV(to_binary(3))),
            (eq(a(one), to_binary(3)), eq(s(Para(Ident(zero), one)), NatV(to_binary(3)))),
            (logic.true, BoolV(logic.true)),
            (eq(b, logic.false), eq(s(Ident(one)), BoolV(logic.false))),
        ]

        for t, res in test_data:
            self.assertEqual(gcl.convert_term(var_map, s, t), res)

    def testMkAssign(self):
        a, b = Var("a", TFun(natT, natT)), Var("b", boolT)
        var_map = {a: 0, b: 1}
        s = Var("s", gcl.stateT)
        test_data = [
            ({a(one): zero}, function.mk_fun_upd(s, Para(Ident(zero), one), NatV(zero))),
            ({b: one}, function.mk_fun_upd(s, Ident(one), NatV(one))),
        ]

        for assign, res in test_data:
            self.assertEqual(gcl.mk_assign(var_map, s, assign), res)


if __name__ == "__main__":
    unittest.main()
