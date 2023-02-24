"""Unit tests for the interval package."""
import unittest

from integral import conditions
from integral.expr import Var
from integral.parser import parse_interval, parse_expr
from integral.interval import Interval, get_bounds_for_expr


class IntervalTest(unittest.TestCase):
    def testParseInterval(self):
        test_data = [
            "(0, 1)", "(0, 1]", "[0, 1)", "[0, 1]",
            "(INT x:[1,2]. 3 * x, 5)",
        ]
        
        for s in test_data:
            self.assertEqual(str(parse_interval(s)), s)

    def testGetBounds(self):
        test_data = [
            # Basic arithmetic
            ("x - 4", "(0, 1)", "(-4, -3)"),
            ("(x + 1) * (x + 2)", "(0, 1)", "(2, 6)"),
            ("(x + 1) * (x + 2)", "(0, 1]", "(2, 6]"),
            ("x ^ 2", "(-oo, oo)", "[0, oo)"),
            ("1 / x ^ 2", "(-oo, oo)", "(0, oo)"),
            ("x + 1", "(-1, -1/2)", "(0, 1/2)"),

            # Square root
            ("sqrt(x)", "(1, 4)", "(1, 2)"),
            ("1 / sqrt(x)", "(1, 4)", "(1/2, 1)"),
            ("1 / sqrt(2 * x)", "(1, 4)", "(1/4 * sqrt(2), 1/2 * sqrt(2))"),
        ]

        for s, i1, i2 in test_data:
            s = parse_expr(s)
            var_range = {Var('x'): parse_interval(i1)}
            self.assertEqual(str(get_bounds_for_expr(s, var_range)), i2)

    def testIntervalPower(self):
        test_data = [(["0","oo",True,True],["2","2",False,False],"(0, oo)")]
        for a,b,res in test_data:
            a[0] = parse_expr(a[0])
            a[1] = parse_expr(a[1])
            b[0] = parse_expr(b[0])
            b[1] = parse_expr(b[1])
            ia = Interval(*a)
            ib = Interval(*b)
            print(ia ** ib)

    def testGetBoundForExpression(self):
        test_data = [
                     (["abs(x) < 1"], "-x^2 + 1", "(0, 1]"),
                     (["k>1","x>1","x < oo"], "x^k", "(1, oo)"),
                     (["m>=0"], "2*m+1", "[1, oo)"),
                     (["x>=1"], "2^x", "[2, oo)"),
                     (["m>=0"], "(2*m+1)/2", "[1/2, oo)"),
                     (["x>=1/2"], "2^x", "[sqrt(2), oo)"),
                     (["x>=1/2","b>0"], "b^x", "(0, oo)"),
                     (["b>-2", "b<2"], "1/4 * b^2", "[0, 1)")
                    ]
        for c, e, res in test_data:
            conds = conditions.Conditions()
            for i in c:
                conds.add_condition(parse_expr(i))
            self.assertEqual(res,str(conds.get_bounds_for_expr(parse_expr(e))))
if __name__ == "__main__":
    unittest.main()
