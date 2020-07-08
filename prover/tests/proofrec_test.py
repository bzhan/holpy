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
            ('(?x1. x = x1 & x1 Mem S) --> x Mem S', '~(S x), ?x1. x = x1 & S x1 |- false'),
            ('(?a1. a = a1 & a1 Mem A) --> a Mem A', '~(A a), ?a1. a = a1 & A a1 |- false'),
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

    """
    Files that have reconstructed successful:

    QF_UF
    ====================================================
    QF_UF/20170829-Rodin/smt249825283571301584.smt2
    QF_UF/20170829-Rodin/smt1300175744189082250.smt2
    QF_UF/20170829-Rodin/smt1468783596909311386.smt2
    QF_UF/20170829-Rodin/smt2080745738819601301.smt2
    QF_UF/20170829-Rodin/smt2325451563592377472.smt2
    QF_UF/20170829-Rodin/smt2598599073465845145.smt2
    QF_UF/20170829-Rodin/smt3166111930664231918.smt2
    QF_UF/20170829-Rodin/smt3534838651727683253.smt2
    QF_UF/20170829-Rodin/smt4057580428149921510.smt2
    QF_UF/20170829-Rodin/smt4458073420585573738.smt2
    QF_UF/20170829-Rodin/smt5144869669709662262.smt2
    QF_UF/20170829-Rodin/smt5490086717622526120.smt2
    QF_UF/20170829-Rodin/smt5801285361354912971.smt2
    QF_UF/20170829-Rodin/smt5832055835117075398.smt2
    QF_UF/20170829-Rodin/smt6739662804326223632.smt2
    QF_UF/20170829-Rodin/smt7452810379672948208.smt2
    QF_UF/20170829-Rodin/smt7632939434921259240.smt2
    QF_UF/20170829-Rodin/smt7665342989239969743.smt2
    QF_UF/20170829-Rodin/smt2061505268723161891.smt2
    QF_UF/20170829-Rodin/smt2080745738819601301.smt2
    QF_UF/20170829-Rodin/smt2970577543992530805.smt2
    
    ======================================================

    diamond
    ======================================================
    eq_diamond2 proof seems to have a bug in and-elim rule.
    ======================================================


    TypeSafe
    ======================================================
    QF_UF/TypeSafe/z3.1184131.smt2
    QF_UF/TypeSafe/z3.1184147.smt2
    QF_UF/TypeSafe/z3.1184163.smt2
    ======================================================

    LIA
    =============================================
    LIA/tptp/NUM917=1.smt2
    LIA/tptp/NUM918=1.smt2
    =============================================
    """

if __name__ == "__main__":
    unittest.main()
