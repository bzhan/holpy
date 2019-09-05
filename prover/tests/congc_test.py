"""Unit test for congruence closure."""

import unittest

from prover import congc
from kernel.type import TVar, TFun
from kernel.term import Term
from kernel.thm import Thm
from logic import basic
from syntax import parser, printer

MERGE, CHECK, EXPLAIN = range(3)

class CongClosureTest(unittest.TestCase):
    def run_test(self, data, verbose=False):
        closure = congc.CongClosure()
        for item in data:
            if item[0] == MERGE:
                _, s, t = item
                closure.merge(s, t)
                if verbose:
                    print("Merge %s, %s\nAfter\n%s" % (s, t, closure))
            elif item[0] == CHECK:
                _, s, t, b = item
                self.assertEqual(closure.test(s, t), b)
            else:
                _, s, t, exp_length = item
                explain = closure.explain(s, t)
                self.assertEqual(sum(len(path) for _, path in explain.items()), exp_length)

    def test1(self):
        self.run_test([
            (MERGE, "t1", "t2"),
            (MERGE, "t3", "t4"),
            (CHECK, "t2", "t4", False),
            (MERGE, "t1", "t3"),
            (CHECK, "t2", "t4", True),
            (EXPLAIN, "t2", "t3", 2),
            (EXPLAIN, "t2", "t4", 3),
        ])

    def test2(self):
        self.run_test([
            (MERGE, ("t1", "t2"), "t3"),
            (MERGE, ("t4", "t5"), "t6"),
            (MERGE, "t1", "t4"),
            (CHECK, "t3", "t6", False),
            (MERGE, "t2", "t5"),
            (CHECK, "t3", "t6", True),
            (EXPLAIN, "t3", "t6", 3),
        ])

    def test3(self):
        self.run_test([
            (MERGE, ("t1", "t2"), "t3"),
            (MERGE, ("t1", "t4"), "t5"),
            (MERGE, "t2", "t4"),
            (CHECK, "t3", "t5", True),
            (EXPLAIN, "t3", "t5", 2),
        ])


class CongClosureHOLTest(unittest.TestCase):
    def run_test(self, data, verbose=False):
        thy = basic.load_theory('logic_base')
        Ta = TVar('a')
        ctxt = {'vars': {
            'a': Ta,
            'b': Ta,
            'c': Ta,
            'd': Ta,
            'f': TFun(Ta, Ta),
            'g': TFun(Ta, Ta),
            "R": TFun(Ta, Ta, Ta),
        }}
        closure = congc.CongClosureHOL(thy)
        for item in data:
            if item[0] == MERGE:
                _, s, t = item
                s = parser.parse_term(thy, ctxt, s)
                t = parser.parse_term(thy, ctxt, t)
                closure.merge(s, t)
                if verbose:
                    print("Merge %s, %s\nAfter\n%s" % (s, t, closure))
            elif item[0] == CHECK:
                _, s, t, b = item
                s = parser.parse_term(thy, ctxt, s)
                t = parser.parse_term(thy, ctxt, t)
                self.assertEqual(closure.test(s, t), b)
            else:
                _, s, t = item
                s = parser.parse_term(thy, ctxt, s)
                t = parser.parse_term(thy, ctxt, t)
                prf = closure.explain(s, t).export()
                self.assertEqual(thy.check_proof(prf), Thm.mk_equals(s, t))
                if verbose:
                    print("Proof of %s" % printer.print_term(thy, Term.mk_equals(s, t)))
                    print(printer.print_proof(thy, prf))

    def test1(self):
        self.run_test([
            (MERGE, "a", "b"),
            (MERGE, "c", "d"),
            (MERGE, "a", "c"),
            (CHECK, "b", "d", True),
            (EXPLAIN, "b", "d"),
        ])

    def test2(self):
        self.run_test([
            (MERGE, "f a", "c"),
            (MERGE, "a", "b"),
            (CHECK, "f b", "c", True),
            (EXPLAIN, "f b", "c"),
        ])

    def test3(self):
        self.run_test([
            (MERGE, "f a", "a"),
            (CHECK, "f (f (f a))", "a", True),
            (EXPLAIN, "f (f (f a))", "a"),
        ])

    def test4(self):
        self.run_test([
            (MERGE, "a", "b"),
            (CHECK, "R (R (f a) (f a)) (f a)", "R (R (f b) (f a)) (f b)", True),
            (EXPLAIN, "R (R (f a) (f a)) (f a)", "R (R (f b) (f a)) (f b)"),
            (CHECK, "R (f a) a", "R a (f a)", False),
            (MERGE, "f a", "a"),
            (CHECK, "R (f a) a", "R a (f a)", True),
            (EXPLAIN, "R (f a) a", "R a (f a)"),
        ])

    def test5(self):
        self.run_test([
            (MERGE, "%x. f x", "%x. g x"),
            (CHECK, "%x. f x", "%x. g x", True),
            (EXPLAIN, "%x. f x", "%x. g x"),
        ])

if __name__ == "__main__":
    unittest.main()
