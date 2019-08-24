import unittest

from integral import latex
from integral.parser import parse_expr


class LatexTest(unittest.TestCase):
    def testConvertExpr(self):
        test_data = [
            ("1/3", "\\frac{1}{3}"),
            ("x^-2", "x ^ {-2}"),
            ("[3 * x]_x=1,2", "\\left. 3 x \\right\\vert_{x=1}^{2}"),
            ("INT x:[2,3]. 2 * x + x ^ 2", "\int_{x=2}^{3} 2 x + x ^ 2 \,\mathrm{dx}"),
            ("(3 * x + 1) ^ -2", "(3 x + 1) ^ {-2}"),
        ]

        for e, res in test_data:
            e = parse_expr(e)
            self.assertEqual(latex.convert_expr(e), res)


if __name__ == "__main__":
    unittest.main()
