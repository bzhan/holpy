import unittest

from integral import latex
from integral.parser import parse_expr


class LatexTest(unittest.TestCase):
    def testConvertExpr(self):
        test_data = [
            ("1/3", "\\frac{1}{3}"),
            ("x^-2", "x ^ {-2}"),
            ("-t^2", "-t ^ 2"),
            ("exp(-1)", "e^{(-1)}"),
            ("-(x + y)", "-(x + y)"),
            ("[3 * x]_x=1,2", "\\left. 3 x \\right\\vert_{x=1}^{2}"),
            ("INT x:[2,3]. 2 * x + x ^ 2", "\int_{2}^{3} 2 x + x ^ 2 \,\mathrm{dx}"),
            ("(3 * x + 1) ^ -2", "(3 x + 1) ^ {-2}"),
            ("INT x:[0,pi / 4]. sin(x)", "\int_{0}^{\pi/4} \sin{(x)} \,\mathrm{dx}"),
            ("x^(1/2)","\sqrt{x}"),
            ("x * (1 + x)", "x (1 + x)"),
            ("INT x:[4,9]. x^(1/2) * (1 + x^(1/2))","\int_{4}^{9} \sqrt{x} (1 + \sqrt{x}) \,\mathrm{dx}"),
            ("cos(x) ^ 2", "\cos^{2}x"),
            ("exp(-(t^2/2))", "e^{(-\\frac{t ^ 2}{2})}")
        ]

        for e, res in test_data:
            e = parse_expr(e)
            self.assertEqual(latex.convert_expr(e), res)


if __name__ == "__main__":
    unittest.main()
