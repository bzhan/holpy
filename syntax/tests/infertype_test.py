# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, Type, BoolType, NatType
from kernel.term import Term, Var, Const, Comb, Abs, Bound, Implies, Lambda, Eq
from logic import basic
from logic import logic
from data import nat
from data.list import listT, cons, mk_append, nil
from logic import context
from syntax.infertype import type_infer, infer_printed_type, TypeInferenceException

Ta = TVar("a")


class InferTypeTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('list')
        context.ctxt = context.Context(vars={
            "A" : BoolType,
            "P" : TFun(Ta, BoolType),
            "a" : Ta,
            "b" : Ta,
        })

    def testInferType(self):
        test_data = [
            # A1 --> A2
            (Const("implies", None)(Var("A1", None), Var("A2", None)),
             Implies(Var("A1", BoolType), Var("A2", BoolType))),
            # A1 = A2
            (Const("equals", None)(Var("A1", BoolType), Var("A2", None)),
             Eq(Var("A1", BoolType), Var("A2", BoolType))),
            # a = b
            (Const("equals", None)(Var("a", None), Var("b", None)),
             Const("equals", TFun(Ta, Ta, BoolType))(Var("a", Ta), Var("b", Ta))),
            # %x. P x
            (Abs("x", None, Var("P", None)(Bound(0))),
             Abs("x", Ta, Var("P", TFun(Ta, BoolType))(Bound(0)))),
            # %x y. x = y
            (Abs("x", Ta, Abs("y", None, Const("equals", None)(Bound(1), Bound(0)))),
             Abs("x", Ta, Abs("y", Ta, Const("equals", TFun(Ta, Ta, BoolType))(Bound(1), Bound(0))))),
            # [a]
            (Const("cons", None)(Var("a", None), Const("nil", None)),
             cons(Ta)(Var("a", Ta), Const("nil", listT(Ta)))),
        ]

        for t, res in test_data:
            self.assertEqual(type_infer(t), res)

    def testInferTypeFail(self):
        test_data = [
            (Const("implies", None)(Var("A1", NatType), Var("A2", None))),
            (Const("equals", None)(Var("A", None), Var("a", None)))
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Unable to unify", type_infer, t)

    def testInferTypeFail2(self):
        test_data = [
            Abs("x", None, Abs("y", None, Const("equals", None)(Var("x", None), Var("y", None)))),
            Const("nil", None),
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Unspecified type", type_infer, t)

    def testInferTypeFail3(self):
        test_data = [
            Var('s', None)(Var('s', None)),
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Infinite loop", type_infer, t)

    def testInferPrintedType(self):
        t = Const("nil", listT(Ta))
        infer_printed_type(t)
        self.assertTrue(hasattr(t, "print_type"))

        t = cons(Ta)(Var("a", Ta))
        infer_printed_type(t)
        self.assertFalse(hasattr(t.fun, "print_type"))

        t = Eq(Const("nil", listT(Ta)), Const("nil", listT(Ta)))
        infer_printed_type(t)
        self.assertFalse(hasattr(t.fun.fun, "print_type"))
        self.assertTrue(hasattr(t.arg1, "print_type"))
        self.assertFalse(hasattr(t.arg, "print_type"))

        t = Eq(mk_append(nil(Ta),nil(Ta)), nil(Ta))
        infer_printed_type(t)
        self.assertTrue(hasattr(t.arg1.arg1, "print_type"))
        self.assertFalse(hasattr(t.arg1.arg, "print_type"))
        self.assertFalse(hasattr(t.arg, "print_type"))

        t = Lambda(Var("x", Ta), Eq(Var("x", Ta), Var("x", Ta)))
        infer_printed_type(t)


if __name__ == "__main__":
    unittest.main()
