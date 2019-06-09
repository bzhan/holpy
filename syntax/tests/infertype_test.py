# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, Type, boolT
from kernel.term import Term, Var, Const, Comb, Abs, Bound
from logic import basic
from logic import logic
from logic import nat
from logic import list
from syntax.infertype import type_infer, infer_printed_type, TypeInferenceException

thy = basic.load_theory('list')

Ta = TVar("a")
listT = list.listT

ctxt = {'vars': {
    "A" : boolT,
    "B" : boolT,
    "C" : boolT,
    "P" : TFun(Ta, boolT),
    "Q" : TFun(Ta, boolT),
    "R" : TFun(Ta, Ta, boolT),
    "a" : Ta,
    "b" : Ta,
    "c" : Ta,
    "f" : TFun(Ta, Ta),
    "nn" : TFun(boolT, boolT),
    "m" : nat.natT,
    "n" : nat.natT,
    "p" : nat.natT,
    "xs" : listT(Ta),
    "ys" : listT(Ta),
    "zs" : listT(Ta),
}}

class InferTypeTest(unittest.TestCase):
    def testInferType(self):
        test_data = [
            # A1 --> A2
            (Const("implies", None)(Var("A1", None), Var("A2", None)),
             Term.mk_implies(Var("A1", boolT), Var("A2", boolT))),
            # A1 = A2
            (Const("equals", None)(Var("A1", boolT), Var("A2", None)),
             Term.mk_equals(Var("A1", boolT), Var("A2", boolT))),
            # a = b
            (Const("equals", None)(Var("a", None), Var("b", None)),
             Const("equals", TFun(Ta, Ta, boolT))(Var("a", Ta), Var("b", Ta))),
            # %x. P x
            (Abs("x", None, Var("P", None)(Bound(0))),
             Abs("x", Ta, Var("P", TFun(Ta, boolT))(Bound(0)))),
            # %x y. x = y
            (Abs("x", Ta, Abs("y", None, Const("equals", None)(Bound(1), Bound(0)))),
             Abs("x", Ta, Abs("y", Ta, Const("equals", TFun(Ta, Ta, boolT))(Bound(1), Bound(0))))),
            # [a]
            (Const("cons", None)(Var("a", None), Const("nil", None)),
             list.cons(Ta)(Var("a", Ta), Const("nil", listT(Ta)))),
        ]

        for t, res in test_data:
            self.assertEqual(type_infer(thy, ctxt, t), res)

    def testInferTypeFail(self):
        test_data = [
            (Const("implies", None)(Var("A1", nat.natT), Var("A2", None))),
            (Const("equals", None)(Var("A", None), Var("a", None)))
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Unable to unify", type_infer, thy, ctxt, t)

    def testInferTypeFail2(self):
        test_data = [
            Abs("x", None, Abs("y", None, Const("equals", None)(Var("x", None), Var("y", None)))),
            Const("nil", None),
        ]

        for t in test_data:
            self.assertRaisesRegex(TypeInferenceException, "Unspecified type", type_infer, thy, ctxt, t)

    def testInferPrintedType(self):
        t = Const("nil", listT(Ta))
        infer_printed_type(thy, t)
        self.assertTrue(hasattr(t, "print_type"))

        t = list.cons(Ta)(Var("a", Ta))
        infer_printed_type(thy, t)
        self.assertFalse(hasattr(t.fun, "print_type"))

        t = Term.mk_equals(Const("nil", listT(Ta)), Const("nil", listT(Ta)))
        infer_printed_type(thy, t)
        self.assertFalse(hasattr(t.fun.fun, "print_type"))
        self.assertTrue(hasattr(t.arg1, "print_type"))
        self.assertFalse(hasattr(t.arg, "print_type"))

        t = Term.mk_equals(list.mk_append(list.nil(Ta),list.nil(Ta)), list.nil(Ta))
        infer_printed_type(thy, t)
        self.assertTrue(hasattr(t.arg1.arg1, "print_type"))
        self.assertFalse(hasattr(t.arg1.arg, "print_type"))
        self.assertFalse(hasattr(t.arg, "print_type"))

        t = Term.mk_abs(Var("x", Ta), Term.mk_equals(Var("x", Ta), Var("x", Ta)))
        infer_printed_type(thy, t)


if __name__ == "__main__":
    unittest.main()
