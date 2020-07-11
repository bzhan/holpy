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
            (RealVal('3/5'), '((3/5)::real)'),
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
            basic.load_theory('real')
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

    def testRecRealSet(self):
        test_data = [
            ('max a b = (1/2) * (a + b + abs(a - b))',
            '~((if a >= b then a else b) = 1 / 2 * (a + b + (if a - b >= 0 then a - b else -(a - b)))) |- false'),
            ('{x. (a <= x & x <= b) & ~(a < x & x < b)} Sub {a, b}',
            '~(x = a | x = b), (a <= x & x <= b) & ~(a < x & x < b) |- false'),
            ('(x Mem T --> 0 <= f x) --> S Sub T --> (if x Mem S then f x else 0) <= (if x Mem T then f x else 0)', 
            '!x1. S x1 --> T x1, T x --> f x >= 0, ~((if S x then f x else 0) <= (if T x then f x else 0)) |- false'),
            ('max (if x Mem S then (1::real) else 0) (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)', 
            '~((if (if S x then (1::int) else 0) >= (if T x then 1 else 0) then if S x then (1::int) else 0 else if T x then 1 else 0) = (if S x | T x then 1 else 0)) |- false'),
            ('min (if x Mem S then (1::real) else 0) (if x Mem T then 1 else 0) = (if x Mem (S Int T) then 1 else 0)',
            '~(~(S x) | ~(T x)), ~((if (if S x then (1::int) else 0) <= (if T x then 1 else 0) then if S x then (1::int) else 0 else if T x then 1 else 0) = (if S x & T x then 1 else 0)) |- false'),
            ('S Int T = empty_set --> (if x Mem S then (1::real) else 0) + (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)',
            '!x1. ~(S x1 & T x1), ~((if S x then (1::int) else 0) + (if T x then 1 else 0) = (if S x | T x then 1 else 0)) |- false'),
            ('S ∪ T = S ∩ T ∪ {x. x ∈ S & ~x ∈ T} ∪ {x. x ∈ T & ~x ∈ S}',
            '~(~(~(S x) | ~(T x)) | ~(T x | ~(S x)) | ~(S x | ~(T x))), ~(S x | T x <--> (S x & T x | S x & ~(T x)) | T x & ~(S x)) |- false'),
            ('(0::real) <= (if x Mem s & 1 / (of_nat n + 1) <= abs (f x) then 1 else 0)',
            '~((if s x & 1 / (rn + 1) <= (if f x >= 0 then f x else -(f x)) then (1::int) else 0) >= 0) |- false'),
            ('(0::real) <= of_nat n + 1', 'rn >= 0, ~(rn + 1 >= 0) |- false'),
            ('1 / (of_nat n + 1) < b --> 1 < (of_nat n + 1) * b', 'rn >= 0, 1 / (rn + 1) < b, ~((rn + 1) * b > 1) |- false'),
            ('a <= of_nat n --> a < of_nat (n + 1)', 'a <= rn, ~(a < rn + 1) |- false'),
            ('~(n = 0) --> of_nat (n - 1) + (1::real) = of_nat n', 'n >= 0, ~(n = 0), ~((if n >= 1 then rn - 1 else 0) + 1 = rn) |- false'),
            ('(1::real) = 0 --> real_inverse a = b', 'false |- false')
        ]

        for t, p in test_data:
            context.set_context('real', vars={
            'a': 'real', 'b': 'real', 'x': 'real', 'f': 'real => real', 'S': 'real set', 'T': 'real set',
            'n': 'nat'})
            t = parse_term(t)
            proof=z3wrapper.solve_and_proof(t)    
            r = proofrec.proofrec(proof)
            basic.load_theory('real')
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


    """
    UNSAT files in QF_UF/2018-Goel-hwbench/
    ==================================================
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_blocks.2.prop1_ab_reg_max.smt2', ✓
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_blocks.3.prop1_ab_reg_max.smt2', ✓
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_bridge.1.prop1_ab_reg_max.smt2', ✓
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_bridge.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_bridge.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.1.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.1.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.2.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.2.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.3.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.3.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.4.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.4.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.5.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.5.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_brp2.6.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_bug-1_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cache_coherence_three_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.1.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.2.prop1_ab_fp_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.2.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.3.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.4.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.5.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.6.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cambridge.7.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_collision.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_collision.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_collision.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_collision.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_collision.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_collision.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_counter_v_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cyclic_scheduler.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cyclic_scheduler.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cyclic_scheduler.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_cyclic_scheduler.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_elevator.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_elevator.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_elevator.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_elevator.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_elevator.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_elevator_planning.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_eq_sdp_v7_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_exit.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_exit.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_exit.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_exit.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_extinction.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_frogs.1.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_frogs.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_gear.1.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_gear.1.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_gear.1.prop4_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_gear.2.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_gear.2.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_gear.2.prop4_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_hanoi.2.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_Heap_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_Arbiter_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_b02_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_b04_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_b04_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_b05_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_b08_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_b08_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_Barrel_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_BufAl_ab_fp_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_Rrobin_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_Rrobin_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_segments_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_Spinner_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_TicTacToe_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_traffic_light_example_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_traffic_light_example_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_TreeArb_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_TreeArb_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_h_Vlunc_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_iprotocol.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_itc99_b12_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_itc99_b13_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lamport.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lann.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_leader_election.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_leader_election.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lifts.8.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_loyd.1.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_loyd.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_loyd.2.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_loyd.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_loyd.3.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_loyd.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lup.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lup.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lup.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_lup.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_msmie.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_msmie.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_msmie.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_msmie.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.1.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.1.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.1.prop4_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.2.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.2.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.2.prop4_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.4.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.4.prop3_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_needham.4.prop4_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_peg_solitaire.1.prop1_ab_fp_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_peg_solitaire.2.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_peg_solitaire.4.prop1_ab_fp_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_peg_solitaire.5.prop1_ab_fp_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_peg_solitaire.6.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.1.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.2.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.3.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.4.prop5_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.4.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.5.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.6.prop5_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.6.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.7.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pgm_protocol.8.prop6_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pipeline_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pj_icu_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pj_icu_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pouring.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_pouring.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_production_cell.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_production_cell.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_protocols.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_protocols.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_protocols.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_protocols.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_protocols.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_reader_writer.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_reader_writer.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_reader_writer.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.1.prop2_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.1.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.1.prop3_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.2.prop2_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.2.prop2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_resistance.2.prop3_ab_cti_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_rether.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_schedule_world.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_schedule_world.2.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_schedule_world.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sokoban.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sokoban.2.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sokoban.3.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_ball2004_1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_ball2004_2_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_loop_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_loop_v_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_state_machine_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_sym_ex_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_sw_sym_ex_v_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_synapse.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_synapse.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_synapse.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_synapse.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_synapse.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_synapse.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_telephony.8.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.1.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.2.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.3.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.4.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.5.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.6.prop1_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.6.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_train-gate.7.prop1_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_usb_phy_ab_reg_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_v_Unidec_ab_br_max.smt2',
    'D:/smt-lib/QF_UF/2018-Goel-hwbench/QF_UF_v_Unidec_ab_fp_max.smt2'
    ==================================================
    
    """







if __name__ == "__main__":
    unittest.main()
