# Author: Bohua Zhan

import unittest

from kernel.term import Term
from kernel.thm import Thm
from kernel.proof import ItemID
from data import nat
from logic import basic
from logic import logic
from data.nat import zero, one, bit0, bit1
from logic.tests.logic_test import test_macro
from logic.tests.conv_test import test_conv
from syntax import parser

thy = basic.load_theory('nat')

class NatTest(unittest.TestCase):
    def testPlus(self):
        self.assertEqual(nat.mk_plus(), zero)
        self.assertEqual(nat.mk_plus(zero), zero)
        self.assertEqual(nat.mk_plus(one), one)
        self.assertEqual(nat.mk_plus(zero, one), nat.plus(zero, one))
        self.assertEqual(nat.mk_plus(*([zero]*3)), nat.plus(nat.plus(zero, zero), zero))

    def testBinary(self):
        test_data = [
            (0, zero),
            (1, one),
            (2, bit0(one)),
            (3, bit1(one)),
            (4, bit0(bit0(one))),
            (5, bit1(bit0(one))),
            (6, bit0(bit1(one))),
            (7, bit1(bit1(one))),
            (19, bit1(bit1(bit0(bit0(one))))),
            (127, bit1(bit1(bit1(bit1(bit1(bit1(one))))))),
        ]

        for n, binary in test_data:
            self.assertEqual(nat.to_binary(n), binary)
            self.assertEqual(nat.from_binary(binary), n)

    def testBinaryLarge(self):
        test_data = [
            100, 10000, 100000, 111111, 999999, 10101010101, 12345678987654321,
        ]

        for n in test_data:
            self.assertEqual(nat.from_binary(nat.to_binary(n)), n)

    def testIsBinary(self):
        test_data = [
            (zero, True),
            (nat.Suc(zero), False),
            (one, True),
            (nat.Suc(one), False),
            (bit0(one), True),
            (bit0(nat.Suc(bit0(one))), False),
            (bit0, False),
            (bit1, False),
        ]

        for n, b in test_data:
            self.assertEqual(nat.is_binary(n), b)

    def testSucConv(self):
        test_data = [
            0, 1, 2, 3, 4, 5, 6, 7, 19, 127, 1000, 1001,
        ]

        for n in test_data:
            t = nat.Suc(nat.to_binary(n))
            t_res = nat.to_binary(n + 1)
            test_conv(self, 'nat', nat.Suc_conv(), t=t, t_res=t_res)

    def testAddConv(self):
        test_data = [
            (0, 2),
            (2, 0),
            (1, 2),
            (2, 1),
            (2, 2),
            (2, 3),
            (3, 2),
            (3, 3),
            (5, 5),
            (10, 5),
            (12345,98765),
        ]

        for m, n in test_data:
            t = nat.mk_plus(nat.to_binary(m), nat.to_binary(n))
            t_res = nat.to_binary(m + n)
            test_conv(self, 'nat', nat.add_conv(), t=t, t_res=t_res)

    def testMultConv(self):
        test_data = [
            (0, 2),
            (2, 0),
            (1, 2),
            (2, 1),
            (2, 2),
            (2, 3),
            (3, 2),
            (3, 3),
            (5, 5),
            (10, 5),
            (123,987),
        ]

        for m, n in test_data:
            t = nat.mk_times(nat.to_binary(m), nat.to_binary(n))
            t_res = nat.to_binary(m * n)
            test_conv(self, 'nat', nat.mult_conv(), t=t, t_res=t_res)

    def testNatConv(self):
        test_data = [
            ("(2::nat) + 3", 5),
            ("Suc (2 + 3)", 6),
            ("Suc (Suc (Suc 0))", 3),
            ("(5::nat) + 2 * 3", 11),
            ("((5::nat) + 2) * 3", 21),
            ("5 * Suc (2 + 5)", 40),
        ]

        for t, n in test_data:
            t_res = nat.to_binary_nat(n)
            test_conv(self, 'nat', nat.nat_conv(), t=t, t_res=t_res)

    def testNormFull(self):
        test_data = [
            ("(x * y) * (z * y)", "x * y * y * z"),
            ("(x + y) + (z + y)", "x + y * 2 + z"),
            ("(x + y) * (y + z)", "x * y + x * z + y * y + y * z"),
            ("(x + y) * (x + y)", "x * x + x * y * 2 + y * y"),
            ("0 + 1 * x + 0 * y", "x"),
            ("x + 2 + y + 3", "x + y + 5"),
            ("3 * x * 5 * x", "x * x * 15"),
            ("(x + 2 * y) * (y + 2 * x)", "x * x * 2 + x * y * 5 + y * y * 2"),
            ("(3::nat) + 5 * 2", "(13::nat)"),
            ("x + Suc y", "x + y + 1"),
            ("Suc (x + Suc y)", "x + y + 2"),
            ("x * Suc y", "x + x * y"),
            ("x * 1 * 1 * 1", "x"),
        ]

        ctxt = {"x": 'nat', "y": 'nat', "z": 'nat'}
        for expr, res in test_data:
            test_conv(self, 'nat', nat.norm_full(), ctxt=ctxt, t=expr, t_res=res)

    def testNormFullLevel1(self):
        thy = basic.load_theory('nat', limit=('thm', 'mult_0_right'))
        test_data = [
            ("y + (x + x * y)", "x + y + x * y"),
            ("z + y + x", "x + y + z"),
            ("1 + y", "y + 1"),
            ("Suc (x + y)", "x + y + 1"),
            ("2 + 3 + x", "x + 2 + 3"),
        ]

        cv = nat.norm_full()
        ctxt = {'vars': {"x": nat.natT, "y": nat.natT, "z": nat.natT}}
        for expr, res in test_data:
            t = parser.parse_term(thy, ctxt, expr)
            t2 = parser.parse_term(thy, ctxt, res)
            res_th = Thm.mk_equals(t, t2)
            prf = cv.get_proof_term(thy, t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

    def testNormFullLevel2(self):
        thy = basic.load_theory('nat', limit=('thm', 'add_cancel_left'))
        test_data = [
            ("(x + y) * (y + x)", "x * x + x * y + x * y + y * y"),
            ("(Suc x) * y", "y + x * y"),
        ]

        cv = nat.norm_full()
        ctxt = {'vars': {"x": nat.natT, "y": nat.natT, "z": nat.natT}}
        for expr, res in test_data:
            t = parser.parse_term(thy, ctxt, expr)
            t2 = parser.parse_term(thy, ctxt, res)
            res_th = Thm.mk_equals(t, t2)
            prf = cv.get_proof_term(thy, t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

    def testNatNormMacro(self):
        test_data = [
            ("x * (y * z) = y * (z * x)"),
            ("Suc (Suc (Suc x)) + y = x + Suc (Suc (Suc y))"),
            ("x + y + (y + z) = y * 2 + (x + z)"),
        ]

        ctxt = {"x": 'nat', "y": 'nat', "z": 'nat'}
        for expr in test_data:
            test_macro(self, 'nat', 'nat_norm', ctxt=ctxt, args=expr, res=expr)

    def testNatIneqMacro(self):
        test_data = [
            (0, 1), (1, 0),
            (0, 2), (2, 0),
            (1, 2), (2, 1),
            (1, 3), (3, 1),
            (2, 3), (3, 2),
            (10, 13), (17, 19), (22, 24),
        ]

        for m, n in test_data:
            goal = "~(%d::nat) = %d" % (m, n)
            test_macro(self, 'nat', 'nat_const_ineq', args=goal, res=goal)

    def testNatEqConv(self):
        test_data = [
            ((0, 0), logic.true),
            ((1, 1), logic.true),
            ((0, 1), logic.false),
        ]

        cv = nat.nat_eq_conv()
        for (a, b), res in test_data:
            t = Term.mk_equals(nat.to_binary_nat(a), nat.to_binary_nat(b))
            prf = cv.get_proof_term(thy, t).export()
            res_th = Thm.mk_equals(t, res)
            self.assertEqual(thy.check_proof(prf), res_th)

    def testNatLessEqMacro(self):
        test_data = [
            (3, 5),
            (4, 4),
        ]

        macro = nat.nat_const_less_eq_macro()
        for m, n in test_data:
            goal = nat.less_eq(nat.to_binary_nat(m), nat.to_binary_nat(n))
            pt = macro.get_proof_term(thy, goal, [])
            prf = pt.export()
            self.assertEqual(thy.check_proof(prf), Thm([], goal))

    def testNatLessMacro(self):
        test_data = [
            (0, 1),
            (3, 5),
        ]

        macro = nat.nat_const_less_macro()
        for m, n in test_data:
            goal = nat.less(nat.to_binary_nat(m), nat.to_binary_nat(n))
            pt = macro.get_proof_term(thy, goal, [])
            prf = pt.export()
            self.assertEqual(thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
