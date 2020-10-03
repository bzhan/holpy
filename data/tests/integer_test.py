import unittest
from data import integer
from kernel import term
from kernel.type import IntType
from logic.tests.logic_test import test_macro
from syntax import parser
from logic import basic

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
            ("x * z * y = x * y * z"),
            ("x - y = x + (-1) * y"),
            ("x - -y = x + y"),
            ("x - --x = 0")
        )

        vars = {"x": "int", "y": "int", "z": "int"}
        for expr in test_data:
            test_macro(self, 'int', 'int_norm', vars=vars, res=expr, args=expr)

    def testIntEqMacro(self):
        test_data = (
            ("x = y * z <--> x = z * y"),
            ("x - 3 > y <--> x - y > 3")
        )

        vars = {"x": "int", "y": "int"}
        for expr in test_data:
            test_macro(self, 'int', 'int_eq_macro', vars=vars, res=expr, args=expr)