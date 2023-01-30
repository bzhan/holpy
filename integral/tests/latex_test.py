import unittest

from integral import latex, expr
from integral.parser import parse_expr


class LatexTest(unittest.TestCase):
    def testConvertExpr(self):
        test_data = [
            ('I(t) ^ -1', 'I^{-1}(t)'),
            ("sqrt(2)", "\\sqrt{2}"),
            ("1/3", "\\frac{1}{3}"),
            ("x^-2", "x ^ {-2}"),
            ("-t^2", "-t ^ {2}"),
            ("exp(-1)", "e^{-1}"),
            ("-(x + y)", "-(x + y)"),
            ("[3 * x]_x=1,2", "\\left. 3 x \\right\\vert_{x=1}^{2}"),
            ("INT x:[2,3]. 2 * x + x ^ 2", "\int_{2}^{3} 2 x + x ^ {2} \,dx"),
            ("(3 * x + 1) ^ -2", "(3 x + 1) ^ {-2}"),
            ("INT x:[0,pi / 4]. sin(x)", "\int_{0}^{\pi/4} \sin{x} \,dx"),
            ("x^(1/2)","\sqrt{x}"),
            ("x * (1 + x)", "x (1 + x)"),
            ("INT x:[4,9]. x^(1/2) * (1 + x^(1/2))","\int_{4}^{9} \sqrt{x} (1 + \sqrt{x}) \,dx"),
            ("cos(x) ^ 2", "\cos^{2}(x)"),
            ("exp(-(t^2/2))", "e^{-t ^ {2}/2}"),
            ("2 * 2 ^ (1/2)", "2 \\sqrt{2}"),
            ("(-1) * exp((-1))", "-1 e^{-1}"),
            ("abs(u) ^ -1", "\left| u \\right| ^ {-1}"),
            ("(3 + x) ^ (3/2)", "(3 + x) ^ {3/2}")
        ]

        for e, res in test_data:
            e = parse_expr(e)
            self.assertEqual(latex.convert_expr(e), res)


if __name__ == "__main__":
    unittest.main()
