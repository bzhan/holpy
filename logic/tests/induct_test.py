# Author: Bohua Zhan

import unittest

from kernel.type import TVar, Type, TFun, boolT
from kernel.term import Var, Const, Term
from kernel.thm import Thm
from kernel import extension
from logic import basic
from logic import logic, induct

imp = Term.mk_implies
eq = Term.mk_equals
all = Term.mk_all
conj = logic.mk_conj
thy = basic.load_theory('logic_base')

class InductTest(unittest.TestCase):
    def testInductNat(self):
        nat = Type("nat")
        nat_ext = induct.add_induct_type(
            "nat", [], [("zero", nat, []), ("Suc", TFun(nat, nat), ["n"])])
        
        zero = Const("zero", nat)
        S = Const("Suc", TFun(nat, nat))
        n = Var("n", nat)
        n2 = Var("n'", nat)
        x = Var("x", nat)
        P = Var("P", TFun(nat, boolT))

        res = [
            extension.Type("nat", 0),
            extension.Constant("zero", nat),
            extension.Constant("Suc", TFun(nat, nat)),
            extension.Theorem("nat_zero_Suc_neq", Thm([], logic.neg(eq(zero, S(n))))),
            extension.Theorem("nat_Suc_inject", Thm([], imp(eq(S(n), S(n2)), eq(n, n2)))),
            extension.Theorem("nat_induct", Thm([], imp(P(zero), all(n, imp(P(n), P(S(n)))), P(x)))),
            extension.Attribute("nat_induct", "var_induct")
        ]

        self.assertEqual(nat_ext.data, res)

    def testInductAdd(self):
        nat = Type("nat")
        plus = Const("nat_plus", TFun(nat, nat, nat))
        zero = Const("zero", nat)
        S = Const("Suc", TFun(nat, nat))
        m = Var("m", nat)
        n = Var("n", nat)

        ext = induct.add_induct_def(
            thy, 'nat_plus', TFun(nat, nat, nat), [
                eq(plus(zero, n), n),
                eq(plus(S(m), n), S(plus(m, n)))])
        
        res = [
            extension.Constant("nat_plus", TFun(nat, nat, nat)),
            extension.Theorem("nat_plus_def_1", Thm([], eq(plus(zero, n), n))),
            extension.Attribute("nat_plus_def_1", "hint_rewrite"),
            extension.Theorem("nat_plus_def_2", Thm([], eq(plus(S(m), n), S(plus(m, n))))),
            extension.Attribute("nat_plus_def_2", "hint_rewrite"),
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
        P = Var("P", TFun(Tlista, boolT))
        xlist = Var("x", Tlista)

        res = [
            extension.Type("list", 1),
            extension.Constant("nil", Tlista),
            extension.Constant("cons", TFun(Ta, Tlista, Tlista)),
            extension.Theorem("list_nil_cons_neq", Thm([], logic.neg(eq(nil, cons(x, xs))))),
            extension.Theorem("list_cons_inject", Thm([], imp(eq(cons(x, xs), cons(x2, xs2)), conj(eq(x, x2), eq(xs, xs2))))),
            extension.Theorem("list_induct", Thm([], imp(P(nil), all(x, all(xs, imp(P(xs), P(cons(x, xs))))), P(xlist)))),
            extension.Attribute("list_induct", "var_induct")
        ]
        self.assertEqual(list_ext.data, res)

    def testInductProd(self):
        Ta = TVar("a")
        Tb = TVar("b")
        Tab = Type("prod", Ta, Tb)
        prod_ext = induct.add_induct_type(
            "prod", ["a", "b"], [("Pair", TFun(Ta, Tb, Tab), ["a", "b"])])

        a = Var("a", Ta)
        b = Var("b", Tb)
        a2 = Var("a'", Ta)
        b2 = Var("b'", Tb)
        pair = Const("Pair", TFun(Ta, Tb, Tab))
        P = Var("P", TFun(Tab, boolT))
        x = Var("x", Tab)

        res = [
            extension.Type("prod", 2),
            extension.Constant("Pair", TFun(Ta, Tb, Tab)),
            extension.Theorem("prod_Pair_inject", Thm([], imp(eq(pair(a, b), pair(a2, b2)), conj(eq(a, a2), eq(b, b2))))),
            extension.Theorem("prod_induct", Thm([], imp(all(a, all(b, P(pair(a, b)))), P(x)))),
            extension.Attribute("prod_induct", "var_induct")
        ]
        self.assertEqual(prod_ext.data, res)

    def testInductPredicate(self):
        nat = Type("nat")
        even = Const("even", TFun(nat, boolT))
        zero = Const("zero", nat)
        Suc = Const("Suc", TFun(nat, nat))
        n = Var("n", nat)
        prop_zero = even(zero)
        prop_Suc = Term.mk_implies(even(n), even(Suc(Suc(n))))
        data = [("even_zero", prop_zero), ("even_Suc", prop_Suc)]
        even_ext = induct.add_induct_predicate(thy, "even", TFun(nat, boolT), data)
        a1 = Var("_a1", nat)
        P = Var("P", boolT)

        res = [
            extension.Constant("even", TFun(nat, boolT)),
            extension.Theorem("even_zero", Thm([], even(zero))),
            extension.Attribute("even_zero", "hint_backward"),
            extension.Theorem("even_Suc", Thm.mk_implies(even(n), even(Suc(Suc(n))))),
            extension.Attribute("even_Suc", "hint_backward"),
            extension.Theorem("even_cases", Thm.mk_implies(even(a1), imp(eq(a1,zero), P), all(n, imp(eq(a1,Suc(Suc(n))), even(n), P)), P))
        ]
        self.assertEqual(even_ext.data, res)


if __name__ == "__main__":
    unittest.main()
