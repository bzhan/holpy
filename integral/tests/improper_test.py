from cgi import test
import unittest

from integral import rules
from integral.rules import FullSimplify, LHopital
from integral.parser import parse_expr
from integral.expr import Limit

class ImproperTest(unittest.TestCase):
    def testNormalize(self):
        test_cases = [
            ("LIM {x -> oo}. x", "oo"),
            ("LIM {x -> oo}. 2 * x", "oo"),
            ("LIM {x -> oo}. exp(x)", "oo"),
            ("LIM {x -> oo}. exp(2 * x)", "oo"),
            ("LIM {x -> oo}. 2 + exp(2 * x)", "oo"),
            ("LIM {x -> oo}. 1 / x", "0"),
            ("LIM {x -> oo}. x ^ (-1)", "0"),
            ("LIM {x -> oo}. 1/x + exp(2*x)", "oo"),
            ("LIM {x -> oo}. exp(1/x)", "1"),
            ("LIM {x -> -oo}. exp(1/x)", "1"),
            ("LIM {x -> oo}. x*exp(-x)", "LIM {x->oo}. x*exp(-x)"),
            ("LIM {x -> oo}. exp(x) - log(x)", "LIM {x->oo}. exp(x) + -log(x)"),
            ("LIM {x -> oo}. x/log(x)", "LIM {x -> oo}. x * log(x) ^ -1"),
            ("LIM {x -> oo}. exp(x+2)/x", "LIM {x -> oo}. x ^ -1 * exp(2 + x)"),
            ("LIM {x -> oo}. x/exp(x+2)", "LIM {x -> oo}. x * exp(-2 + -x)"),
            ("LIM {t -> -oo}. -1 + -(t * exp(t)) + exp(t)", "-1 + (LIM {t -> -oo}. -(t * exp(t)))")
            # ("LIM {x -> 1}. 1/(x-1)", "oo")
        ]
        for t, t_res in test_cases:
            t = parse_expr(t)
            t_res = parse_expr(t_res)
            self.assertEqual(t.normalize(), t_res)

    def testLHopital(self):
        test_cases = [
            "LIM {t -> -oo}. -(t * exp(t))"
        ]

        t = test_cases[0]
        t = parse_expr(t)
        t0 = rules.OnLocation(rules.LimFunExchange(), '').eval(t)
        # print("t0:", t0)
        t1 = rules.OnLocation(rules.Mul2Div(1), '0.0').eval(t0)
        # print("t1:", t1)
        t2 = rules.OnLocation(rules.Simplify(), '0.0.1').eval(t1)
        # print("t2:", t2)
        t3 = rules.OnLocation(rules.LHopital(), '0').eval(t2)
        # print("t3:", t3)
        t4 = rules.OnLocation(rules.LimitSimplify(), '0').eval(t3)
        # print("t4:", t4)
        t5 = rules.OnLocation(rules.Simplify(), '').eval(t4)
        # print("t5:", t5)
        self.assertEqual(str(t5),'0')

    # def test_improper_integration(self):
    #     test_case = [
    #         ("LIM {t -> inf}. INT x:[1,t]. 1 / x ^ 2", "LIM {t -> inf}. 1 + -(t ^ -1)"),
    #     ]

    #     for t, t_res in test_case:
    #         simp_rule = FullSimplify()
    #         t_res = parse_expr(t_res)
    #         t = parse_expr(t)
    #         self.assertEqual(simp_rule.eval(t), t_res)

    # def test_det_pos_inf(self):
    #     test_cases = [
    #         ("7 * x ^ (-1)", "oo", False),
    #         ("9 + -7 * x ^ -2", "oo", False),
    #         ("1/x", "0", True)
    #     ]

    #     for p, lim, res in test_cases:
    #         p = parse_expr(p)
    #         lim = parse_expr(lim)
    #         self.assertEqual(Limit("x", lim, p).is_pos_inf(), res)

    # def test_lhopital(self):
    #     test_case = [
    #         ("(x^2 - 1) / (x^2 + 3*x - 4)", "1", "2/5"),
    #         ("(x - 4) / (sqrt(x) - 2)", "4", "4"),
    #         ("sin(x) / x", "0", "1"),
    #         ("(1/x - 1/3) / (x^2 - 9)", "3", "-1/54"),
    #         ("(3 + log(x)) / (x^2 + 7)", "inf", "0"),
    #         ("exp(3*x)/ (5*x + 200)", "inf", "inf"),
    #         # ("(x^2 + 3*x - 10)/(7*x^2 - 5*x + 4)", "inf", "1/7"),
    #         ("(log(x))^2 / (exp(2*x))", "inf", "0"),
    #         # ("(exp(x) + 2/x) / (exp(x) + 5/x)", "inf", "1")
    #         ("x*exp(-x)", "inf", "0"),
    #         ("log(t)/(1/t)", "0", "0")
    #     ]

    #     for p, l, res in test_case:
    #         p = parse_expr(p)
    #         l = parse_expr(l)
    #         print("p: %s\n norm_p: %s\n" % (p, p.normalize_frac()))
    #         res = parse_expr(res)
    #         lim_l_p = Limit("x", l, p)
    #         self.assertEqual(lim_l_p.lh(), res)
            


if __name__ == "__main__":
    unittest.main()

