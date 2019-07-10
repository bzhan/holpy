# Author: Bohua Zhan

import unittest

from kernel.term import Var, Term
from logic import basic
from logic.logic import neg, true
from data.int import plus, minus, times, zero, one, intT, less_eq, less
from imperative.com import Skip, Assign, Seq, Cond, While
from imperative.parser2 import cond_parser

thy = basic.load_theory('int')
eq = Term.mk_equals

class ComTest(unittest.TestCase):
    def testPrintCom(self):
        x = Var('x', intT)
        test_data = [
            (Skip(), "skip"),
            (Assign("x", plus(x,one)), "x := x + 1"),
            (Seq(Assign("x", plus(x,one)), Assign("x", plus(x,one))),
             "x := x + 1;\nx := x + 1"),
            (Cond(eq(x,one), Skip(), Assign("x", plus(x,one))),
             "if (x == 1) then\n  skip\nelse\n  x := x + 1"),
            (While(eq(x,one), true, Assign("x", plus(x,one))),
             "while (x == 1) {\n  [true]\n  x := x + 1\n}")
        ]

        for com, s in test_data:
            self.assertEqual(com.print_com(thy), s)

    def testComputeWP(self):
        a = Var('a', intT)
        b = Var('b', intT)
        test_data = [
            (Skip(), "a <= m", "a <= m"),
            (Assign("m", plus(a,b)), "a <= m", "a <= a + b"),
            (Seq(Assign("m", plus(a,b)), Assign("n", minus(a,b))),
             "a <= m & n <= a", "a  <= a + b & a - b <= a"),
        ]

        for c, post, pre in test_data:
            post = cond_parser.parse(post)
            pre = cond_parser.parse(pre)
            self.assertEqual(c.compute_wp(post), pre)

    def testVCG(self):
        a = Var('a', intT)
        b = Var('b', intT)
        A = Var('A' ,intT)
        B = Var('B', intT)
        test_data = [
            (Seq(Assign("m", plus(a,b)), Assign("n", minus(a,b))),
             "0 <= b", "a <= m & n <= a",
             ["0 <= b --> a <= a + b & a - b <= a"]),

            (While(less(zero,a), less_eq(zero,a), Assign("a", minus(a,one))),
             "0 <= a", "a == 0",
             ["0 <= a --> 0 <= a",
              "0 <= a & 0 < a --> 0 <= a - 1",
              "0 <= a & ~0 < a --> a == 0"]),

            (While(neg(eq(a,A)), eq(b,times(a,B)), Seq(Assign('b',plus(b,B)), Assign('a',plus(a,one)))),
             "a == 0 & b == 0", "b == A * B",
             ["a == 0 & b == 0 --> b == a * B",
              "b == a * B & a != A --> b + B == (a + 1) * B",
              "b == a * B & ~a != A --> b == A * B"]),

            (Cond(neg(eq(a,zero)), Assign('a',zero), Skip()),
             "true", "a == 0",
             ["true --> if a != 0 then 0 == 0 else a == 0"]),
        ]

        for c, pre, post, vcs in test_data:
            pre = cond_parser.parse(pre)
            post = cond_parser.parse(post)
            vcs = [cond_parser.parse(vc) for vc in vcs]
            c.pre = [pre]
            c.compute_wp(post)
            self.assertEqual(c.get_vc(), vcs)
            print(c.print_com(thy))


if __name__ == "__main__":
    unittest.main()
