# Author: Bohua Zhan

import unittest

from kernel.type import TFun, BoolType, NatType
from kernel.term import Var, Term, Eq, true, false, Binary
from logic import basic
from logic import logic
from data import nat
from data import function
from paraverifier import gcl
from paraverifier.gcl import Para, Ident, NatV, BoolV
from syntax import printer


zero = nat.zero
one = nat.one

class GCLTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('gcl')

    def testConvertTerm(self):
        a, b = Var("a", TFun(NatType, NatType)), Var("b", BoolType)
        var_map = {a: 0, b: 1}
        s = Var("s", gcl.stateT)
        test_data = [
            (a(one), s(Para(Ident(zero), one))),
            (b, s(Ident(one))),
            (Binary(3), NatV(Binary(3))),
            (Eq(a(one), Binary(3)), Eq(s(Para(Ident(zero), one)), NatV(Binary(3)))),
            (true, BoolV(true)),
            (Eq(b, false), Eq(s(Ident(one)), BoolV(false))),
        ]

        for t, res in test_data:
            self.assertEqual(gcl.convert_term(var_map, s, t), res)

    def testMkAssign(self):
        a, b = Var("a", TFun(NatType, NatType)), Var("b", BoolType)
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
