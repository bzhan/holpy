# Author: Bohua Zhan

import unittest

from kernel.term import Var, Term
from logic import basic
from logic import logic
from data.int import plus, minus, one, intT
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
            (While(eq(x,one), logic.true, Assign("x", plus(x,one))),
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
             "a <= m & n <= a", "a <= a + b & a - b <= a"),
        ]

        for com, post, pre in test_data:
            post = cond_parser.parse(post)
            pre = cond_parser.parse(pre)
            self.assertEqual(com.compute_wp(post), pre)

    def testVCG(self):
        a = Var('a', intT)
        b = Var('b', intT)
        test_data = [
            (Seq(Assign("m", plus(a,b)), Assign("n", minus(a,b))),
             "a <= m & n <= a", "0 <= b",
             ["0 <= b --> a <= a + b & a - b <= a"]),
        ]

        for com, post, pre, vcs in test_data:
            post = cond_parser.parse(post)
            pre = cond_parser.parse(pre)
            vcs = [cond_parser.parse(vc) for vc in vcs]
            com.pre = [pre]
            com.compute_wp(post)
            self.assertEqual(com.get_vc(), vcs)


if __name__ == "__main__":
    unittest.main()
