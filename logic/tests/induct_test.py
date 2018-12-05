# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun, hol_bool
from kernel.term import Var, Const, Term
from kernel.thm import Thm
from kernel.extension import AxType, AxConstant, Theorem
from logic.logic import Logic
from logic import induct

imp = Term.mk_implies
eq = Term.mk_equals
all = Term.mk_all
conj = Logic.mk_conj

class InductTest(unittest.TestCase):
    def testInductNat(self):
        nat = Type("nat")
        nat_ext = induct.add_induct_type(
            "nat", [], [("0", nat, []), ("Suc", TFun(nat, nat), ["n"])])
        
        zero = Const("0", nat)
        S = Const("Suc", TFun(nat, nat))
        n = Var("n", nat)
        n2 = Var("n'", nat)
        x = Var("x", nat)
        P = Var("P", TFun(nat, hol_bool))

        res = [
            AxType("nat", 0),
            AxConstant("0", nat),
            AxConstant("Suc", TFun(nat, nat)),
            Theorem("nat_0_Suc_neq", Thm([], Logic.neg(eq(zero, S(n))))),
            Theorem("nat_Suc_inject", Thm([], imp(eq(S(n), S(n2)), eq(n, n2)))),
            Theorem("nat_induct", Thm([], imp(P(zero), all(n, imp(P(n), P(S(n)))), P(x))))
        ]
        self.assertEqual(nat_ext.data, res)

    def testInductAdd(self):
        nat = Type("nat")
        plus = Const("plus", TFun(nat, nat, nat))
        zero = Const("0", nat)
        S = Const("Suc", TFun(nat, nat))
        m = Var("m", nat)
        n = Var("n", nat)

        ext = induct.add_induct_def(plus, [
            Thm([], eq(plus(zero, n), n)),
            Thm([], eq(plus(S(m), n), S(plus(m, n))))])
        
        res = [
            AxConstant("plus", TFun(nat, nat, nat)),
            Theorem("plus_def_1", Thm([], eq(plus(zero, n), n))),
            Theorem("plus_def_2", Thm([], eq(plus(S(m), n), S(plus(m, n)))))
        ]
        self.assertEqual(ext.data, res)

    def testInductList(self):
        Ta = TVar("a")
        Tlista = Type("list", Ta)
        list_ext = induct.add_induct_type(
            "list", ["a"], [("nil", Tlista, []), ("cons", TFun(Ta, Tlista, Tlista), ["x", "xs"])])

        nil = Const("nil", Tlista)
        cons = Const("cons", TFun(Ta, Tlista, Tlista))
        x = Var("x", Ta)
        xs = Var("xs", Tlista)
        x2 = Var("x'", Ta)
        xs2 = Var("xs'", Tlista)
        P = Var("P", TFun(Tlista, hol_bool))
        xlist = Var("x", Tlista)

        res = [
            AxType("list", 1),
            AxConstant("nil", Tlista),
            AxConstant("cons", TFun(Ta, Tlista, Tlista)),
            Theorem("list_nil_cons_neq", Thm([], Logic.neg(eq(nil, cons(x, xs))))),
            Theorem("list_cons_inject", Thm([], imp(eq(cons(x, xs), cons(x2, xs2)), conj(eq(x, x2), eq(xs, xs2))))),
            Theorem("list_induct", Thm([], imp(P(nil), all(x, all(xs, imp(P(xs), P(cons(x, xs))))), P(xlist))))
        ]
        self.assertEqual(list_ext.data, res)

if __name__ == "__main__":
    unittest.main()
