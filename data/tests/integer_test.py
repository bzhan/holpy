import unittest
from data import integer
from logic.tests.logic_test import test_macro
from syntax import parser
from logic import basic

basic.load_theory('int')

class IntegerTest(unittest.TestCase):
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