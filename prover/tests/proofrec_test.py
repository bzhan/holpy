import unittest

from z3 import IntVal, RealVal, BoolVal, Function, IntSort, BoolSort, Context, Solver, Ints, set_param, And as zAnd
from z3 import Const as zConst, Int as zInt
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

basic.load_theory('nat')

class ProofrecTest(unittest.TestCase):
    def testTranslateTerm(self):
        Z = IntSort()
        B = BoolSort()
        F = Function('F', Z, Z)
        x = zInt('x')
        test_data = [
            (IntVal(0), True, '(0::nat)'),
            (IntVal(10), True, '(10::nat)'),
            # (IntVal(-3), False, '(-3::int)'),
            # (RealVal('3/5'), False, '((3/5)::real)'),
            (BoolVal(True), False, 'true'),
            (BoolVal(False), False, 'false'),
            (zInt('x'), True, 'x'),
            # (zInt('y'), False, 'y'),
            (F, True, 'F'),
            (F(0) * x, True, 'F(0) * x'),
        ]

        for i, j, k in test_data:
            context.set_context('nat', vars={'x':'nat', 'F':'nat=>nat'})
            k = parse_term(k)
            vars = ['x']
            self.assertEqual(proofrec.translate(i, vars), k)

    def testRec1(self):
        context.set_context('nat', vars={"s": 'nat => nat', "A": 'nat', "B": 'nat'})
        t = parse_term('s 0 = 0 & s 1 = 0 --> s 1 = s 0 * B')
        proof=z3wrapper.solve_and_proof(t)    
        r = proofrec.proofrec(proof)
        self.assertEqual(str(r.th), '~(s 1 = s 0 * B), s 0 = 0 & s 1 = 0 |- false')

if __name__ == "__main__":
    unittest.main()
