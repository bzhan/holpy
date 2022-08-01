"""Unit tests for limit."""

from fractions import Fraction
from msilib.schema import Condition
import unittest
from integral.conditions import Conditions

from integral.expr import Var, Const, POS_INF, NEG_INF
from integral import limits
from integral.limits import Unknown, PolyLog, Exp, Limit
from integral.limits import UNKNOWN, LESS, GREATER, EQUAL
from integral.limits import AT_CONST, FROM_ABOVE, FROM_BELOW, TWO_SIDED
from integral import parser


class LimitsTest(unittest.TestCase):
    def testAsympCompare(self):
        test_data = [
            (Unknown(), PolyLog(1), UNKNOWN),
            (PolyLog(1), PolyLog(2), LESS),
            (PolyLog(1), PolyLog(1, 1), LESS),
            (PolyLog(2), PolyLog(1, 1), GREATER),
            (PolyLog(2), Exp(PolyLog(1)), LESS),
            (Exp(PolyLog(1)), Exp(PolyLog(1, 1)), LESS),
            (PolyLog(Var("n")), PolyLog(Var("n")), EQUAL),
            (PolyLog(Var("n")), PolyLog(1), UNKNOWN),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.asymp_compare(a, b), res)

    def testAsympAdd(self):
        test_data = [
            (Unknown(), PolyLog(1), Unknown()),
            (PolyLog(1), Unknown(), Unknown()),
            (PolyLog(1), PolyLog(2), PolyLog(2)),
            (PolyLog(Var("n")), PolyLog(1), Unknown()),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.asymp_add(a, b), res)

    def testAsympMult(self):
        test_data = [
            (Unknown(), PolyLog(1), Unknown()),
            (PolyLog(1), Unknown(), Unknown()),
            (PolyLog(1), PolyLog(1), PolyLog(2)),
            (PolyLog(1), PolyLog(0, 1), PolyLog(1, 1)),
            (Exp(PolyLog(1)), Exp(PolyLog(1, 1)), Exp(PolyLog(1, 1))),
            (Exp(PolyLog(1)), PolyLog(1), Exp(PolyLog(1))),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.asymp_mult(a, b), res)

    def testAsympDiv(self):
        test_data = [
            (PolyLog(1, 1), PolyLog(1), PolyLog(0, 1)),
            (PolyLog(2), PolyLog(0, 1), PolyLog(2, -1)),
            (Exp(PolyLog(1, 1)), Exp(PolyLog(1)), Exp(PolyLog(1, 1))),
            (Exp(PolyLog(1)), PolyLog(1), Exp(PolyLog(1))),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.asymp_div(a, b), res)

    def testAsympPower(self):
        test_data = [
            (Unknown(), Const(2), Unknown()),
            (PolyLog(1), Const(2), PolyLog(2)),
            (PolyLog(1, 1), Const(2), PolyLog(2, 2)),
            (Exp(PolyLog(1)), Const(2), Exp(PolyLog(1))),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.asymp_power(a, b), res)

    def testExpAsymp(self):
        test_data = [
            (Unknown(), Unknown()),
            (PolyLog(1), Exp(PolyLog(1))),
            (Exp(PolyLog(1)), Exp(Exp(PolyLog(1)))),
        ]

        for a, res in test_data:
            self.assertEqual(limits.exp_asymp(a), res)

    def testLimitAdd(self):
        test_data = [
            (Limit(None), Limit(2), Limit(None)),
            (Limit(POS_INF, asymp=PolyLog(2)), Limit(POS_INF, asymp=PolyLog(1)),
             Limit(POS_INF, asymp=PolyLog(2))),
            (Limit(POS_INF, asymp=PolyLog(Var("n"))), Limit(POS_INF, asymp=PolyLog(1)), Limit(POS_INF)),
            (Limit(POS_INF, asymp=PolyLog(2)), Limit(NEG_INF, asymp=PolyLog(2)), Limit(None)),
            (Limit(POS_INF, asymp=PolyLog(2)), Limit(NEG_INF, asymp=PolyLog(1)),
             Limit(POS_INF, asymp=PolyLog(2))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(NEG_INF, asymp=PolyLog(2)),
             Limit(NEG_INF, asymp=PolyLog(2))),
            (Limit(POS_INF, asymp=PolyLog(Var("n"))), Limit(NEG_INF, asymp=PolyLog(1)), Limit(None)),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(POS_INF, asymp=PolyLog(2)),
             Limit(POS_INF, asymp=PolyLog(2))),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(NEG_INF, asymp=PolyLog(2)),
             Limit(NEG_INF, asymp=PolyLog(2))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(2), Limit(POS_INF, asymp=PolyLog(1))),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(2), Limit(NEG_INF, asymp=PolyLog(1))),
            (Limit(0, asymp=PolyLog(1)), Limit(0, asymp=PolyLog(2)), Limit(0, asymp=PolyLog(2))),
            (Limit(0, side=AT_CONST), Limit(2, side=AT_CONST), Limit(2, side=AT_CONST)),
            (Limit(0, asymp=PolyLog(1), side=FROM_ABOVE), Limit(0, asymp=PolyLog(2), side=FROM_BELOW),
             Limit(0, asymp=PolyLog(1), side=FROM_ABOVE)),
            (Limit(0, asymp=PolyLog(2), side=FROM_ABOVE), Limit(0, asymp=PolyLog(1), side=FROM_BELOW),
             Limit(0, asymp=PolyLog(1), side=FROM_BELOW)),
            (Limit(0, asymp=PolyLog(Var("n")), side=FROM_ABOVE), Limit(0, asymp=PolyLog(2), side=FROM_BELOW),
             Limit(0, side=TWO_SIDED)),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.limit_add(a, b), res)

    def testLimitUMinus(self):
        test_data = [
            (Limit(None), Limit(None)),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(NEG_INF, asymp=PolyLog(1))),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(POS_INF, asymp=PolyLog(1))),
            (Limit(2, asymp=PolyLog(1)), Limit(-2, asymp=PolyLog(1))),
            (Limit(2, side=AT_CONST), Limit(-2, side=AT_CONST)),
            (Limit(2, asymp=PolyLog(1), side=FROM_ABOVE), Limit(-2, asymp=PolyLog(1), side=FROM_BELOW)),
            (Limit(2, asymp=PolyLog(1), side=FROM_BELOW), Limit(-2, asymp=PolyLog(1), side=FROM_ABOVE)),
        ]

        for a, res in test_data:
            self.assertEqual(limits.limit_uminus(a), res)

    def testLimitMult(self):
        test_data = [
            (Limit(None), Limit(2), Limit(None)),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(POS_INF, asymp=PolyLog(2)),
             Limit(POS_INF, asymp=PolyLog(3))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(NEG_INF, asymp=PolyLog(2)),
             Limit(NEG_INF, asymp=PolyLog(3))),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(NEG_INF, asymp=PolyLog(2)),
             Limit(POS_INF, asymp=PolyLog(3))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(2), Limit(POS_INF, asymp=PolyLog(1))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(-2), Limit(NEG_INF, asymp=PolyLog(1))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(-2), Limit(NEG_INF, asymp=PolyLog(1))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(0, asymp=PolyLog(2)),
             Limit(0, asymp=PolyLog(1))),
            (Limit(POS_INF, asymp=PolyLog(2)), Limit(0, asymp=PolyLog(1)),
             Limit(POS_INF, asymp=PolyLog(1))),
            (Limit(POS_INF, asymp=Exp(PolyLog(1))), Limit(0, asymp=PolyLog(Var("n"))),
             Limit(POS_INF, asymp=Exp(PolyLog(1)))),
            (Limit(0, asymp=Exp(PolyLog(1))), Limit(POS_INF, asymp=PolyLog(Var("n"))),
             Limit(0, asymp=Exp(PolyLog(1)))),
            (Limit(0, asymp=Exp(PolyLog(1)), side=FROM_ABOVE), Limit(POS_INF, asymp=PolyLog(Var("n"))),
             Limit(0, asymp=Exp(PolyLog(1)), side=FROM_ABOVE)),
            (Limit(0, asymp=Exp(PolyLog(1)), side=FROM_ABOVE), Limit(NEG_INF, asymp=PolyLog(Var("n"))),
             Limit(0, asymp=Exp(PolyLog(1)), side=FROM_BELOW)),
            (Limit(0, asymp=PolyLog(1)), Limit(0, asymp=PolyLog(2)), Limit(0, asymp=PolyLog(3))),
            (Limit(0, asymp=PolyLog(1), side=FROM_ABOVE), Limit(0, asymp=PolyLog(2), side=FROM_BELOW),
             Limit(0, asymp=PolyLog(3), side=FROM_BELOW)),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.limit_mult(a, b), res)

    def testLimitInverse(self):
        test_data = [
            (Limit(None), Limit(None)),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(0, asymp=PolyLog(1), side=FROM_ABOVE)),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(0, asymp=PolyLog(1), side=FROM_BELOW)),
            (Limit(0), Limit(None)),
            (Limit(0, side=FROM_ABOVE), Limit(POS_INF)),
            (Limit(0, asymp=PolyLog(1), side=FROM_BELOW), Limit(NEG_INF, asymp=PolyLog(1))),
            (Limit(2, side=AT_CONST), Limit(Fraction(1, 2), side=AT_CONST)),
            (Limit(2, asymp=PolyLog(1)), Limit(Fraction(1, 2), asymp=PolyLog(1))),
            (Limit(2, asymp=PolyLog(1), side=FROM_ABOVE),
             Limit(Fraction(1, 2), asymp=PolyLog(1), side=FROM_BELOW)),
            (Limit(2, asymp=PolyLog(1), side=FROM_BELOW),
             Limit(Fraction(1, 2), asymp=PolyLog(1), side=FROM_ABOVE)),
        ]

        for a, res in test_data:
            self.assertEqual(limits.limit_inverse(a), res)

    def testLimitPower(self):
        test_data = [
            (Limit(None), Limit(2), Limit(None)),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(2), Limit(POS_INF, asymp=PolyLog(2))),
            (Limit(POS_INF, asymp=PolyLog(1)), Limit(-2), Limit(0, asymp=PolyLog(2), side=FROM_ABOVE)),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(2), Limit(POS_INF, asymp=PolyLog(2))),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(3), Limit(NEG_INF, asymp=PolyLog(3))),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(-2), Limit(0, asymp=PolyLog(2), side=FROM_ABOVE)),
            (Limit(NEG_INF, asymp=PolyLog(1)), Limit(-3), Limit(0, asymp=PolyLog(3), side=FROM_BELOW)),
            (Limit(2), Limit(POS_INF, asymp=PolyLog(1)), Limit(POS_INF, asymp=Exp(PolyLog(1)))),
            (Limit(2), Limit(NEG_INF, asymp=PolyLog(1)), Limit(0, asymp=Exp(PolyLog(1)), side=FROM_ABOVE)),
            (Limit(2), Limit(3, side=AT_CONST), Limit(8)),
            (Limit(-2), Limit(3, side=AT_CONST), Limit(-8)),
            (Limit(0, side=AT_CONST), Limit(POS_INF), Limit(0, side=AT_CONST)),
            (Limit(0, asymp=PolyLog(1), side=FROM_ABOVE), Limit(2),
             Limit(0, asymp=PolyLog(2), side=FROM_ABOVE)),
            (Limit(0, asymp=PolyLog(1), side=FROM_ABOVE), Limit(-2), Limit(POS_INF, asymp=PolyLog(2))),
            (Limit(0, asymp=PolyLog(1), side=FROM_BELOW), Limit(2, side=AT_CONST),
             Limit(0, asymp=PolyLog(2), side=FROM_ABOVE)),
            (Limit(0, asymp=PolyLog(1), side=FROM_BELOW), Limit(3, side=AT_CONST),
             Limit(0, asymp=PolyLog(3), side=FROM_BELOW)),
            (Limit(0, asymp=PolyLog(1), side=TWO_SIDED), Limit(2, side=AT_CONST),
             Limit(0, asymp=PolyLog(2), side=TWO_SIDED)),
        ]

        for a, b, res in test_data:
            self.assertEqual(limits.limit_power(a, b), res)

    def testLimitOfExpr(self):
        test_data = [
            ("x ^ 2", "oo"),
            ("(x ^ 2 + 1) / x", "oo"),
            ("(x + 1) / (x ^ 2)", "0"),
            ("(x ^ 3 + x ^ 2 + 1) / (x ^ 2 + 3)", "oo"),
            ("(x ^ 2 + 2) / (x ^ 2 + 1)", None),
            ("exp(x) / (x ^ 2)", "oo"),
            ("-exp(x) / (x ^ 2)", "-oo"),
            ("exp(-x) * (x ^ 2)", "0"),
        ]

        for a, res in test_data:
            a = parser.parse_expr(a)
            l = limits.limit_of_expr(a, "x")
            if res is None:
                self.assertIsNone(l.e)
            else:
                res = parser.parse_expr(res)
                self.assertEqual(l.e, res)

    def testLimitOfExprConds(self):
        test_data = [
            ("exp(x) / (x ^ n)", "oo", "n > 0"),
            ("exp(-x) * (x ^ n)", "0", "n > 0"),
            ("exp(x) * (x ^ n)", "oo", "n < 0"),
            ("exp(-x) / (x ^ n)", "0", "n < 0"),
        ]

        for a, res, cond in test_data:
            conds = Conditions()
            conds.add_condition("n", parser.parse_expr(cond))
            a = parser.parse_expr(a)
            l = limits.limit_of_expr(a, "x", conds=conds)
            if res is None:
                self.assertIsNone(l.e)
            else:
                res = parser.parse_expr(res)
                self.assertEqual(l.e, res)


if __name__ == "__main__":
    unittest.main()
