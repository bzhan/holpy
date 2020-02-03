"""Unit test for congruence closure."""

import unittest

from prover import congc
from kernel.type import TVar, TFun, NatType
from kernel.term import Term, Eq
from kernel.thm import Thm
from kernel import theory
from logic import basic
from syntax import parser, printer
from logic import context

MERGE, CHECK, EXPLAIN, MATCH = range(4)

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
            elif item[0] == EXPLAIN:
                _, s, t, exp_length = item
                explain = closure.explain(s, t)
                self.assertEqual(sum(len(path) for _, path in explain.items()), exp_length)
            elif item[0] == MATCH:
                _, pat, t, res = item
                self.assertEqual(closure.ematch(pat, t), res)
            else:
                raise NotImplementedError

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

    def test4(self):
        self.run_test([
            (MERGE, ("t1", "t2"), "t3"),
            (MATCH, ("t1", "?x1"), "t3", [{"?x1": "t2"}]),
            (MERGE, ("t4", "t5"), "t3"),
            (MATCH, ("?x1", "t5"), "t3", [{"?x1": "t4"}]),
            (MERGE, "t1", "t4"),
            (MERGE, "t2", "t5"),
            (MATCH, ("?x1", "?x2"), "t3", [{"?x1": "t4", "?x2": "t5"}]),
        ])


class CongClosureHOLTest(unittest.TestCase):
    def run_test(self, data, verbose=False):
        Ta = TVar('a')
        context.set_context('nat', vars={
            'a': Ta,
            'b': Ta,
            'c': Ta,
            'd': Ta,
            'f': TFun(Ta, Ta),
            'g': TFun(Ta, Ta),
            'R': TFun(Ta, Ta, Ta),
            'm': NatType,
            'n': NatType,
            'p': NatType,
            'q': NatType,
            'x': NatType,
            'y': NatType,
            'z': NatType
        })
        closure = congc.CongClosureHOL()
        for item in data:
            if item[0] == MERGE:
                _, s, t = item
                s = parser.parse_term(s)
                t = parser.parse_term(t)
                closure.merge(s, t)
                if verbose:
                    print("Merge %s, %s\nAfter\n%s" % (s, t, closure))
            elif item[0] == CHECK:
                _, s, t, b = item
                s = parser.parse_term(s)
                t = parser.parse_term(t)
                self.assertEqual(closure.test(s, t), b)
            elif item[0] == EXPLAIN:
                _, s, t = item
                s = parser.parse_term(s)
                t = parser.parse_term(t)
                prf = closure.explain(s, t).export()
                self.assertEqual(theory.thy.check_proof(prf), Thm([], Eq(s, t)))
                if verbose:
                    print("Proof of %s" % Eq(s, t))
                    print(printer.print_proof(prf))
            elif item[0] == MATCH:
                _, pat, t, res = item
                pat = parser.parse_term(pat)
                t = parser.parse_term(t)
                for res_inst in res:
                    for k in res_inst:
                        res_inst[k] = parser.parse_term(res_inst[k])
                inst = closure.ematch(pat, t)
                self.assertEqual(inst, res)
            else:
                raise NotImplementedError

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

    def test6(self):
        self.run_test([
            (MATCH, "(x + y) + z", "p + q", []),
            (MERGE, "m + n", "p"),
            (MATCH, "(x + y) + z", "p + q", [{'x': 'm', 'y': 'n', 'z': 'q'}]),
        ])


if __name__ == "__main__":
    unittest.main()
