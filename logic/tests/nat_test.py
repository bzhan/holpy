# Author: Bohua Zhan

import unittest

from kernel.thm import Thm
from logic import nat
from logic import basic
from logic.nat import zero, one, bit0, bit1
from syntax import parser

thy = basic.loadTheory('nat')

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
            (nat.Suc(zero), True),
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

        cv = nat.Suc_conv()
        for n in test_data:
            t = nat.Suc(nat.to_binary(n))
            res_th = Thm.mk_equals(t, nat.to_binary(n + 1))
            self.assertEqual(cv(t), res_th)
            prf = cv.get_proof_term(t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

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

        cv = nat.add_conv()
        for m, n in test_data:
            t = nat.mk_plus(nat.to_binary(m), nat.to_binary(n))
            res_th = Thm.mk_equals(t, nat.to_binary(m + n))
            self.assertEqual(cv(t), res_th)
            prf = cv.get_proof_term(t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

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

        cv = nat.mult_conv()
        for m, n in test_data:
            t = nat.mk_times(nat.to_binary(m), nat.to_binary(n))
            res_th = Thm.mk_equals(t, nat.to_binary(m * n))
            self.assertEqual(cv(t), res_th)
            prf = cv.get_proof_term(t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

    def testNatConv(self):
        test_data = [
            ("2 + 3", 5),
            ("Suc (2 + 3)", 6),
            ("Suc (Suc (Suc 0))", 3),
            ("5 + 2 * 3", 11),
            ("(5 + 2) * 3", 21),
            ("5 * Suc (2 + 5)", 40),
        ]

        cv = nat.nat_conv()
        for expr, n in test_data:
            t = parser.parse_term(thy, {}, expr)
            res_th = Thm.mk_equals(t, nat.to_binary(n))
            self.assertEqual(cv(t), res_th)
            prf = cv.get_proof_term(t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

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
            ("3 + 5 * 2", "13"),
            ("x + Suc y", "x + y + 1"),
            ("Suc (x + Suc y)", "x + y + 2"),
            ("x * Suc y", "x + x * y"),
            ("x * 1 * 1 * 1", "x"),
        ]

        cv = nat.norm_full()
        ctxt = {"x": nat.natT, "y": nat.natT, "z": nat.natT}
        for expr, res in test_data:
            t = parser.parse_term(thy, ctxt, expr)
            t2 = parser.parse_term(thy, ctxt, res)
            res_th = Thm.mk_equals(t, t2)
            prf = cv.get_proof_term(t).export()
            self.assertEqual(thy.check_proof(prf), res_th)

    def testNatNormMacro(self):
        test_data = [
            ("x * (y * z) = y * (z * x)"),
            ("Suc (Suc (Suc x)) + y = x + Suc (Suc (Suc y))"),
            ("x + y + (y + z) = y * 2 + (x + z)"),
        ]

        macro = nat.nat_norm_macro()
        ctxt = {"x": nat.natT, "y": nat.natT, "z": nat.natT}
        for expr in test_data:
            goal = parser.parse_term(thy, ctxt, expr)
            prf = macro.expand(0, goal)
            self.assertEqual(thy.check_proof(prf), Thm([], goal))


if __name__ == "__main__":
    unittest.main()
