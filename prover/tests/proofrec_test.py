import unittest

from z3 import IntVal, RealVal, BoolVal, Function, IntSort, BoolSort, Context, Solver, Ints, set_param, And as zAnd
from z3 import Const as zConst, Int as zInt
import z3
from prover import z3wrapper, proofrec
from kernel.type import BoolType, NatType, TFun, TVar, STVar, IntType
from kernel.term import Var, And, Implies, Inst, NatVars, Eq, equals, SVar, Const, TFun, Nat, Int,\
                            Real, true, false
from kernel.report import ProofReport
from kernel import theory
from kernel.thm import Thm
from logic import basic
from logic import matcher, context
from kernel.proofterm import ProofTerm
from data import nat
from fractions import Fraction
from syntax.parser import parse_term

basic.load_theory('int')

class ProofrecTest(unittest.TestCase):
    def testTranslateTerm(self):
        Z = IntSort()
        B = BoolSort()
        F = Function('F', Z, Z)
        x = zInt('x')
        y = zInt('y')
        # Focus on nat case now.
        test_data = [
            # (IntVal(0), '(0::int)'),
            # (IntVal(10), '(10::int)'),
            # (IntVal(-3), '(-3::int)'),
            # (RealVal('3/5'), '((3/5)::real)'),
            (BoolVal(True), 'true'),
            (BoolVal(False), 'false'),
            (zInt('x'), 'x'),
            (x + (-1) * y, 'x + (-1) * y'),
            (x + y, 'x + y'),
            (x - y, 'x - y'),
            (x - (-1) * y, 'x - (-1) * y'),
            (zInt('y'), 'y'),
            (F, 'F'),
            (F(0) * x, 'F(0) * x'),
        ]

        for i, k in test_data:
            context.set_context('int', vars={'x':'int', 'y':'int',  'F':'int=>int'})
            k = parse_term(k)
            vars = ['x', 'y']
            self.assertEqual(proofrec.translate(i), k)

    def testRec1(self):
        test_data = [
            ('s 0 = 0 & s 1 = 0 --> s 1 = s 0 * B', 
            '~(s 1 = s 0 * B), s 0 = 0 & s 1 = 0 |- false'),
            ('s 1 = s 0 * B & ~~s 0 = A --> s 1 = A * B', 
            '~(s 1 = A * B), s 1 = s 0 * B & s 0 = A |- false'),
            ('s 1 = s 0 * B & ~s 0 = A --> s 1 + B = (s 0 + 1) * B',
            '~(s 1 + B = (s 0 + 1) * B), s 1 = s 0 * B & ~(s 0 = A) |- false'),
            ('A * B + 1 = 1 + B * A', '~(A * B + 1 = 1 + B * A) |- false'),
            ('s 0 + s 1 = A --> A + s 2 = B --> s 0 + s 2 + s 1 = B', 
            's 0 + s 1 = A, A + s 2 = B, ~(s 0 + s 2 + s 1 = B) |- false'),
            ('(!n. s n = 0) --> s 2 = 0', '!n. s n = 0, ~(s 2 = 0) |- false')
        ]


        for t, p in test_data:    
            context.set_context('nat', vars={"s": 'nat => nat', "A": 'nat', "B": 'nat'})
            t = parse_term(t)
            proof=z3wrapper.solve_and_proof(t)    
            r = proofrec.proofrec(proof)
            basic.load_theory('int')
            self.assertEqual(str(r.th), p)

    def testRecSolveSet(self):
        test_data = [
            ('x Mem S --> S Sub T --> x Mem T', 'S x, ~(T x), !x1. S x1 --> T x1 |- false'),
            ('m Mem univ', '~true |- false'),
            ('x Mem (diff S T) --> x Mem S', '~(S x), S x & ~(T x) |- false'),
        ]


        for t, p in test_data:
            context.set_context('set', vars={
            'm': 'nat', 'S': 'nat set', 'T': 'nat set', 'x': 'nat',
            'a': "'a", 'A': "'a set"})
            t = parse_term(t)
            proof=z3wrapper.solve_and_proof(t)    
            r = proofrec.proofrec(proof)
            self.assertEqual(str(r.th), p)

    def testQuantIntro(self):
        ctx = z3.Context()
        u,v,w = z3.Ints('u v w',ctx=ctx)
        f = z3.ForAll([u,v],z3.Exists(w, u - w == v))
        s = z3.Solver(ctx=ctx)
        s.add(z3.Not(f))
        s.check()
        proofrec.proofrec(s.proof())

if __name__ == "__main__":
    unittest.main()
