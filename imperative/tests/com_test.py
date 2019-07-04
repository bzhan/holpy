# Author: Bohua Zhan

import unittest

from kernel.term import Var, Term
from logic import basic
from logic import logic
from data.nat import plus, one, natT
from imperative.com import Skip, Assign, Seq, Cond, While

thy = basic.load_theory('nat')
eq = Term.mk_equals

class ComTest(unittest.TestCase):
    def testPrintCom(self):
        x = Var('x', natT)
        test_data = [
            (Skip(), "skip"),
            (Assign("x", plus(x,one)), "x := x + 1"),
            (Seq(Assign("x", plus(x,one)), Assign("x", plus(x,one))),
             "x := x + 1;\nx := x + 1"),
            (Cond(eq(x,one), Skip(), Assign("x", plus(x,one))),
             "if (x = 1) then\n  skip\nelse\n  x := x + 1"),
            (While(eq(x,one), logic.true, Assign("x", plus(x,one))),
             "while (x = 1) {\n  [true]\n  x := x + 1\n}")
        ]

        for com, s in test_data:
            self.assertEqual(com.print_com(thy), s)


if __name__ == "__main__":
    unittest.main()
