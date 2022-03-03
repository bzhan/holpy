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

basic.load_theory('smt')

class ProofrecTest(unittest.TestCase):
    # def testTranslateTerm(self):
    #     Z = IntSort()
    #     B = BoolSort()
    #     F = Function('F', Z, Z)
    #     x = zInt('x')
    #     y = zInt('y')
    #     # Focus on nat case now.
    #     test_data = [
    #         # (IntVal(0), '(0::int)'),
    #         # (IntVal(10), '(10::int)'),
    #         # (IntVal(-3), '(-3::int)'),
    #         (RealVal('3/5'), '((3/5)::real)'),
    #         (BoolVal(True), 'true'),
    #         (BoolVal(False), 'false'),
    #         (zInt('x'), 'x'),
    #         (x + (-1) * y, 'x + (-1) * y'),
    #         (x + y, 'x + y'),
    #         (x - y, 'x - y'),
    #         (x - (-1) * y, 'x - (-1) * y'),
    #         (zInt('y'), 'y'),
    #         (F, 'F'),
    #         (F(0) * x, 'F(0) * x'),
    #     ]

    #     for i, k in test_data:
    #         context.set_context('int', vars={'x':'int', 'y':'int',  'F':'int=>int'})
    #         basic.load_theory('real')
    #         k = parse_term(k)
    #         vars = ['x', 'y']
    #         self.assertEqual(proofrec.translate(i), k)

    def testRec1(self):
        test_data = [
            # ('s 0 = 0 & s 1 = 0 --> s 1 = s 0 * B', 
            # '~(s 1 = s 0 * B), s 0 = 0 & s 1 = 0 |- false'),
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
            context.set_context('smt', vars={"s": 'nat => nat', "A": 'nat', "B": 'nat'})
            t = parse_term(t)
            proof, assertions = z3wrapper.solve_and_proof(t)    
            r = proofrec.proofrec(proof, assertions=assertions, trace=True)
            self.assertNotEqual(r.rule, 'sorry')

    def testRecSolveSet(self):
        test_data = [
            ('x Mem S --> S Sub T --> x Mem T', 'S x, ~(T x), !x1. S x1 --> T x1 |- false'),
            ('m Mem univ', '~true |- false'),
            ('x Mem (diff S T) --> x Mem S', '~(S x), S x & ~(T x) |- false'),
            ('(?x1. x = x1 & x1 Mem S) --> x Mem S', '~(S x), ?x1. x = x1 & S x1 |- false'),
            ('(?a1. a = a1 & a1 Mem A) --> a Mem A', '~(A a), ?a1. a = a1 & A a1 |- false'),
        ]


        for t, p in test_data:
            context.set_context('smt', vars={
            'm': 'nat', 'S': 'nat set', 'T': 'nat set', 'x': 'nat',
            'a': "'a", 'A': "'a set"})
            t = parse_term(t)
            proof, assertions = z3wrapper.solve_and_proof(t)
            r = proofrec.proofrec(proof, assertions=assertions, trace=True)
            self.assertNotEqual(r.rule, 'sorry')

    # def testRecRealSet(self):
    #     test_data = [
    #         # ('max a b = (1/2) * (a + b + abs(a - b))',
    #         # '~((if a >= b then a else b) = 1 / 2 * (a + b + (if a - b >= 0 then a - b else -(a - b)))) |- false'),
    #         # ('{x. (a <= x & x <= b) & ~(a < x & x < b)} Sub {a, b}',
    #         # '~(x = a | x = b), (a <= x & x <= b) & ~(a < x & x < b) |- false'),
    #         # ('(x Mem T --> 0 <= f x) --> S Sub T --> (if x Mem S then f x else 0) <= (if x Mem T then f x else 0)', 
    #         # '!x1. S x1 --> T x1, T x --> f x >= 0, ~((if S x then f x else 0) <= (if T x then f x else 0)) |- false'),
    #         # ('max (if x Mem S then (1::real) else 0) (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)', 
    #         # '~((if (if S x then (1::int) else 0) >= (if T x then 1 else 0) then if S x then (1::int) else 0 else if T x then 1 else 0) = (if S x | T x then 1 else 0)) |- false'),
    #         # ('min (if x Mem S then (1::real) else 0) (if x Mem T then 1 else 0) = (if x Mem (S Int T) then 1 else 0)',
    #         # '~(~(S x) | ~(T x)), ~((if (if S x then (1::int) else 0) <= (if T x then 1 else 0) then if S x then (1::int) else 0 else if T x then 1 else 0) = (if S x & T x then 1 else 0)) |- false'),
    #         # ('S Int T = empty_set --> (if x Mem S then (1::real) else 0) + (if x Mem T then 1 else 0) = (if x Mem (S Un T) then 1 else 0)',
    #         # '!x1. ~(S x1 & T x1), ~((if S x then (1::int) else 0) + (if T x then 1 else 0) = (if S x | T x then 1 else 0)) |- false'),
    #         # ('S ∪ T = S ∩ T ∪ {x. x ∈ S & ~x ∈ T} ∪ {x. x ∈ T & ~x ∈ S}',
    #         # '~(~(~(S x) | ~(T x)) | ~(T x | ~(S x)) | ~(S x | ~(T x))), ~(S x | T x <--> (S x & T x | S x & ~(T x)) | T x & ~(S x)) |- false'),
    #         # ('(0::real) <= (if x Mem s & 1 / (of_nat n + 1) <= abs (f x) then 1 else 0)',
    #         # '~((if s x & 1 / (rn + 1) <= (if f x >= 0 then f x else -(f x)) then (1::int) else 0) >= 0) |- false'),
    #         # ('(0::real) <= of_nat n + 1', 'rn >= 0, ~(rn + 1 >= 0) |- false'),
    #         ('1 / (of_nat n + 1) < b --> 1 < (of_nat n + 1) * b', 'rn >= 0, 1 / (rn + 1) < b, ~((rn + 1) * b > 1) |- false'),
    #         # ('a <= of_nat n --> a < of_nat (n + 1)', 'a <= rn, ~(a < rn + 1) |- false'),
    #         # ('~(n = 0) --> of_nat (n - 1) + (1::real) = of_nat n', 'n >= 0, ~(n = 0), ~((if n >= 1 then rn - 1 else 0) + 1 = rn) |- false'),
    #         # ('(1::real) = 0 --> real_inverse a = b', 'false |- false')
    #     ]

    #     for t, p in test_data:
    #         context.set_context('smt', vars={
    #         'a': 'real', 'b': 'real', 'x': 'real', 'f': 'real => real', 'S': 'real set', 'T': 'real set',
    #         'n': 'nat'})
    #         t = parse_term(t)
    #         proof, assertions = z3wrapper.solve_and_proof(t)
    #         r = proofrec.proofrec(proof, assertions=assertions, trace=True)
    #         # self.assertNotEqual(r.rule, 'sorry')
    #         # if r.rule == 'sorry':
    #         #     print(r)
    #         # print(r)

    # def testQuantIntro(self):
    #     ctx = z3.Context()
    #     u,v,w = z3.Ints('u v w',ctx=ctx)
    #     f = z3.ForAll([u,v],z3.Exists(w, u - w == v))
    #     s = z3.Solver(ctx=ctx)
    #     s.add(z3.Not(f))
    #     s.check()
    #     proofrec.proofrec(s.proof())

    def testRewriteInt(self):
        test_data = [
            # bakery
            "false ∨ false ∨ false ∨ true ∨ ¬(x_8 = uclid_ZERO) ∨ ¬(x_7 + -1 * x_5 = 1)\
            ∨ ¬(x_6 = x_5) ∨ ¬(x_9 = uclid_ZERO) ⟷ true",
            
            "~(x_10 ∨ x_11 ∨ ¬x_12 ∨ x_13 ∨ k3 ∨ ~(uclid_ZERO + -1 * x_8 = -1) ∨ \
            ~(uclid_ZERO + -1 * x_7 = 0) ∨ ~(uclid_ZERO + -1 * x_6 = -1))\
            ⟷\
            ~(x_10 ∨ x_11 ∨ ¬x_12 ∨ x_13 ∨ ~(uclid_ZERO + -1 * x_7 ≤ 0) ∨ k3 ∨ \
            ~(uclid_ZERO + -1 * x_7 ≥ 0) ∨ ~(uclid_ZERO + -1 * x_8 ≤ -1) ∨ ~(uclid_ZERO + -1 * x_8 ≥ -1) \
            ∨ ~(uclid_ZERO + -1 * x_6 ≤ -1) ∨ ~(uclid_ZERO + -1 * x_6 ≥ -1))",

            # "¬(x_15 ∨ x_16 ∨ x_17 ∨ x_25 ∨ x_26 ∨ x_27 ∨ x_59 ∨ x_60 ∨ x_61 ∨ ¬(x_3 ∨ ¬x_22) \
            # ∨ ¬(¬x_3 ∨ x_22) ∨ ¬(x_4 ∨ ¬x_23) ∨ ¬(¬x_4 ∨ x_23) ∨ ¬(x_5 ∨ ¬x_24) ∨ ¬(¬x_5 ∨ x_24)) \
            # ⟷ ¬(x_25 ∨ x_26 ∨ x_27 ∨ x_22 ∨ x_23 ∨ x_24 ∨ x_59 ∨ x_60 ∨ x_61)",
            
            "(if hash_1 x1 = hash_2 x1 then hash_2 x1 else hash_1 x1 + hash_1 x1) = (if hash_1 x1 = hash_2 x1 then hash_2 x1 else 2 * hash_1 x1)"
        ]

        context.set_context('smt', vars={
            "x_10": "bool", "x_11": "bool", "x_12": "bool", "x_13": "bool", "k3": "bool", "k2": "bool",
            "x_8": "int", "x_7": "int", "x_5": "int", "x_6": "int", "x_9": "int", "uclid_ZERO": "int",
            "hash_1": "int => int", "hash_2": "int => int", "x1": "int"
        })

        for tm in test_data:
            tm = parse_term(tm)
            pt = proofrec._rewrite(tm)
            self.assertNotEqual(pt.rule, "sorry")

    def testRewriteReal(self):
        test_data = [
            "(x_11 ∧ x_12) ∧ ¬(x_13 - cvclZero = 1) ∨ (x_16 ∧ x_17) ∧ ¬(x_13 - cvclZero = 2) ⟷ x_11 ∧ x_12 ∧ ¬(x_13 + -1 * cvclZero = 1) ∨ x_16 ∧ x_17 ∧ ¬(x_13 + -1 * cvclZero = 2)",
            "¬(x_13 - cvclZero = 3) ⟷ ¬(x_13 + -1 * cvclZero = 3)",
            "(x_14 ∧ x_15) ∧ ¬(x_13 + -1 * cvclZero = 3) ⟷ x_14 ∧ x_15 ∧ ¬(x_13 + -1 * cvclZero = 3)",
            "(x_11 ∧ x_12 ∧ ¬(x_13 + -1 * cvclZero = 1) ∨ x_16 ∧ x_17 ∧ ¬(x_13 + -1 * cvclZero = 2)) ∨ x_14 ∧ x_15 ∧ ¬(x_13 + -1 * cvclZero = 3) ⟷ x_11 ∧ x_12 ∧ ¬(x_13 + -1 * cvclZero = 1) ∨ x_16 ∧ x_17 ∧ ¬(x_13 + -1 * cvclZero = 2) ∨ x_14 ∧ x_15 ∧ ¬(x_13 + -1 * cvclZero = 3)",
            "(x_11 ∧ x_12 ∧ ¬(x_13 + -1 * cvclZero = 1) ∨ x_16 ∧ x_17 ∧ ¬(x_13 + -1 * cvclZero = 2) ∨ x_14 ∧ x_15 ∧ ¬(x_13 + -1 * cvclZero = 3)) ∨ x_0 ∧ x_1 ∧ ¬(x_9 + -1 * cvclZero = 1) ⟷ x_0 ∧ x_1 ∧ ¬(x_9 + -1 * cvclZero = 1) ∨ x_11 ∧ x_12 ∧ ¬(x_13 + -1 * cvclZero = 1) ∨ x_16 ∧ x_17 ∧ ¬(x_13 + -1 * cvclZero = 2) ∨ x_14 ∧ x_15 ∧ ¬(x_13 + -1 * cvclZero = 3)",
            "(if false then (3::real) else 2) = 2",
            "x_46 = (if false then 2 else 1) ⟷ x_46 = 1",
            # "(if x_3 then x_2 else if x_7 + -1 * x_42 ≥ 0 ∨ ¬(x_9 + -1 * x_42 ≥ 0) ∨ x_2 ≥ 3 then x_2 else 1 + x_2) =\
            #  (if x_3 ∨ x_7 + -1 * x_42 ≥ 0 ∨ ¬(x_9 + -1 * x_42 ≥ 0) ∨ x_2 ≥ 3 then x_2 else 1 + x_2)",
            # "(if x_1 then x_4 else if x_10 + -1 * x_42 ≥ 0 ∨ ¬(x_12 + -1 * x_42 ≥ 0) ∨ x_4 ≥ 3 then x_4 else 1 + x_4) =\
            #  (if x_1 ∨ x_10 + -1 * x_42 ≥ 0 ∨ ¬(x_12 + -1 * x_42 ≥ 0) ∨ x_4 ≥ 3 then x_4 else 1 + x_4)",
            # "(if x_2 then x_5 else if x_10 + -1 * x_43 ≥ 0 ∨ x_5 ≥ 3 ∨ ¬(x_12 + -1 * x_43 ≥ 0) then x_5 else 1 + x_5) =\
            #  (if x_2 ∨ x_10 + -1 * x_43 ≥ 0 ∨ x_5 ≥ 3 ∨ ¬(x_12 + -1 * x_43 ≥ 0) then x_5 else 1 + x_5)",
            # "x_0 = 1 ∧ (if x_8 then 2 else x_0) = 2 ⟷ x_0 = 1 ∧ (x_8 ∨ x_0 = 2)",
            # "(if x_7 then 1 else x_0) = 2 ⟷ ¬x_7 ∧ x_0 = 2)",
        ]

        context.set_context('smt', vars={
            "x_11": "bool", "x_12": "bool", "x_16": "bool", "x_17": "bool",
            "x_13": "real", "cvclZero": "real", "x_46": "real",
            # "x_0": "real", "x_8": "bool", "x_7": "bool",
        })

        for tm in test_data:
            tm = parse_term(tm)
            pt = proofrec._rewrite(tm)
            self.assertNotEqual(pt.rule, "sorry")


    def testThLemmaIntSingle(self):
        test_data = [
            # ¬(y ≤ 3), y ≤ 4 ⊢ 0 = -4 + y,
            # y ≥ 0, y ≤ 0 ⊢ 1 = 1 + y,
            # y ≥ 0, ¬(y ≥ 1) ⊢ 1 = 1 + y,
            "x ≥ 1 ∨ x ≤ 0",
            "¬(x ≥ 2) ∨ ¬(x ≤ 0)",
            "¬(x ≥ 1) ∨ ¬(x ≤ 0)",
            "¬(x ≤ 2) ∨ x ≤ 3",
            "¬(x ≤ 3) ∨ ¬(x ≥ 4)",
            "¬(x = 4) ∨ x ≤ 4",
            "¬(1 = x) ∨ x ≥ 1",
            "¬(x ≤ 0) ∨ 4 + x = (if x ≤ 0 then 4 + x else -1 + x)",
            "1 = x ∨ ¬(x ≤ 1) ∨ ¬(x ≥ 1)",
            "3 = -1 + x ∨ ¬(-1 + x ≤ 3) ∨ ¬(-1 + x ≥ 3)",
            "x = 3 ∨ ¬(x ≤ 3) ∨ ¬(x ≥ 3)",
            # "x ≥ 4 ∨ 1 + x = (if x ≥ 4 then -4 + x else 1 + x)",
            # "¬(4 + x = (if x ≤ 0 then 4 + x else -1 + x)) ∨ 4 + x + -1 * (if x ≤ 0 then 4 + x else -1 + x) ≥ 0)",
            # "¬(-1 + x = (if x ≤ 0 then 4 + x else -1 + x)) ∨ -1 + x + -1 * (if x ≤ 0 then 4 + x else -1 + x) ≥ 0)",
            "¬(Succ x = 3) ∨ Succ x ≤ 3",
            "¬(Sum (Pred x) (Succ y) ≥ 2) ∨ ¬(Sum (Pred x) (Succ y) ≤ 1)",
            "¬(Sum (Pred x) (Succ y) = 2) ∨ Sum (Pred x) (Succ y) ≥ 2",
        ]
        
        context.set_context('smt', vars={
            "x" : "int", "Succ": "int => int", "Pred": "int => int", "Sum": "int => int => int"}
        )
        for tm in test_data:
            tm = parse_term(tm)
            self.assertNotEqual(proofrec.th_lemma([tm]).rule, 'sorry')

    def testThLemmaIntMulti(self):
        test_data = [
            (('¬(x ≤ 3)', 'x ≤ 4'), '0 = -4 + x'),
            (('x ≥ 0', 'x ≤ 0'), '1 = 1 + x'),
            (('x ≥ 0', '¬(x ≥ 1)'), '1 = 1 + x')
        ]

        context.set_context('smt', vars={'x': 'int'})

        for assms, res in test_data:
            assms = [ProofTerm.assume(parse_term(assm)) for assm in assms]
            res = parse_term(res)
            self.assertEqual(proofrec.th_lemma([*assms, res]).prop, res)

    def testRewriteIntWithAsserstion(self):
        test_data = [
            ("¬(¬(¬(¬P8 ∨ ¬(F20 + -1 * F18 ≤ 0)) ∨ ¬(P8 ∨ ¬(F4 + -1 * F2 ≤ 0))) ∨ ¬(¬(P8 ∨ ¬(F6 + -1 * F4 ≤ 0)) ∨ \
            ¬(¬P8 ∨ ¬(F22 + -1 * F20 ≤ 0))) ∨ ¬(¬(P8 ∨ ¬(F2 + -1 * F0 ≤ 0)) ∨ ¬(¬P8 ∨ ¬(F18 + -1 * F16 ≤ 0))))\
            ⟷ ¬(¬(F2 + -1 * F0 ≤ 0) ∨ ¬(F6 + -1 * F4 ≤ 0) ∨ ¬(F4 + -1 * F2 ≤ 0))", ("P8", "P8 ⟷ false"))
        ]

        context.set_context('smt', vars={
            "P8": "bool", "F20": "int", "F18": "int",
            "P8": "bool", "F4": "int", "F2": "int", "F6": "int", "F22" : "int", "F20": "int", "F2": "int", "F16": "int",
            "F0": "int"
        })
        for tm, ast in test_data:
            tm = parse_term(tm)
            var, prop = [parse_term(i) for i in ast]
            proofrec.atoms.clear()
            proofrec.atoms[var] = ProofTerm.assume(prop)
            proofrec._rewrite(tm)

    def testDefAxiom(self):
        test_data = [
            "y ≤ 0 ∨ -1 + y = (if y ≤ 0 then 4 + y else -1 + y)",
            "¬(y ≤ 0) ∨ 4 + y = (if y ≤ 0 then 4 + y else -1 + y)",
            '¬(y + x ≥ 10) ∨ -10 + y + x = (if y + x ≥ 10 then -10 + y + x else y + x)',
            # "Succ x + (if x ≤ 0 then 4 + x else -1 + x) ≥ 5 ∨ Succ x + (if x ≤ 0 then 4 + x else -1 + x) = (if Succ x + (if x ≤ 0 then 4 + x else -1 + x) ≥ 5 then -5 + Succ x + (if x ≤ 0 then 4 + x else -1 + x) else Succ x + (if x ≤ 0 then 4 + x else -1 + x))",

        ]
        
        context.set_context('real', vars={
            "y": "int"
        })

        for tm in test_data:
            tm = parse_term(tm)
            self.assertNotEqual(proofrec.def_axiom(tm).rule, 'sorry')

if __name__ == "__main__":
    unittest.main()
