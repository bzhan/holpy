import unittest
from data import integer
from kernel import term
from kernel.type import IntType
from logic.tests.logic_test import test_macro
from logic.tests.conv_test import test_conv
from syntax import parser
from logic import basic, context

basic.load_theory('int')

class IntegerTest(unittest.TestCase):
    def testDestPlus(self):
        x = term.Var('x', IntType)
        y = term.Var('y', IntType)
        z = term.Var('z', IntType)

        test_data = [
            (x + y, [x, y]),
            (x + y + z, [x, y, z]),
            (x * y, [x*y]),
            (x + y - z, [x+y-z])
        ]

        for r, res in test_data:
            self.assertEqual(integer.strip_plus(r), res)

    def testIntNormMacro(self):
        test_data = (
            ("x * z * y", "x * y * z"),
            ("x - y", "x + (-1) * y"),
            ("x - -y", "x + y"),
            ("x - --x", "(0::int)")
        )

        vars = {"x": "int", "y": "int", "z": "int"}
        context.set_context('int', vars=vars)
        for t, t_res in test_data:
            t, t_res = parser.parse_term(t), parser.parse_term(t_res)
            test_conv(self, 'int', integer.int_norm_conv(), vars=vars, t=t, t_res=t_res)

    def testSimplexFormConv(self):
        test_data = (
            ("x + 3 * y > 4", "1 * x + 3 * y >= 5"),
            ("x + 3 * y > -x + 3 * y", "2 * x >= 1"),
            ("x - 2 * y + 4 * z - 3 < x + 5 * z - 4", "-2 * y + -1 * z <= -2"),
            ("x - y + z >= 6 * y", "1 * x + -7 * y + 1 * z >= 0"),
            ("x + y <= x + y", "(0::int) <= 0"),
            ("x + 6 * z >= x + 6 * z", "(0::int) >= 0"),
            ("x + -2 * y >= x + -2 * y - 4", "(4::int) >= 0")
        )

        vars = {"x": "int", "y": "int", "z": "int"}
        context.set_context('int', vars=vars)
        for t, t_res in test_data:
            t, t_res = parser.parse_term(t), parser.parse_term(t_res)
            test_conv(self, 'int', integer.int_simplex_form(), vars=vars, t=t, t_res=t_res)
