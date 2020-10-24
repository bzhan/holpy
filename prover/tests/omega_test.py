import unittest
from kernel import term
from kernel.type import IntType
# from prover.omega import Factoid, negate_key, combine_real_factoid, combine_dark_factoid, factoid_gcd,\
#     dest_plus, dest_times, term_to_factoid, database
from prover.omega import *

class OmegaTest(unittest.TestCase):
    """
    For now, we assume that there is at least one var in inequality.
    """

    def testFactoidKey(self):
        test_data = [
            ([1,2], (1,)),
            ([1,2,3,4], (1,2,3))
        ]

        for r, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.key, res)

    def testFactoidConst(self):
        test_data = [
            ([1,2], 2),
            ([1,2,3,4], 4)
        ]
        for r, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.constant, res)

    def testSplitFactoid(self):
        test_data = [
            ([1,2], ((1,), 2)),
            ([1,2,4,3,5], ((1,2,4,3), 5))
        ]

        for r, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.split_factoid(), res)

    def testZeroVarFactoid(self):
        test_data = [
            ([1,2,3,4], False),
            ([0,0,0,3], True),
            ([0,0,0,0], True)
        ]

        for r, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.is_zero_var_factoid(), res)

    def testFalseFactoid(self):
        test_data = [
            ([1,2,0,0,-3], False),
            ([0,0,-3], True),
            ([0,0,3], False)
        ]

        for r, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.is_false_factoid(), res)

    def testTrueFactoid(self):
        test_data = [
            ([0,0,100], True),
            ([0,1,100], False),
            ([0,0,-99], False)
        ]        

        for r, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.is_true_factoid(), res)

    def testEvalFactoidRHS(self):
        test_data = [
            ([1, 3, -2, 4], {0:3, 1:2, 2:6}, 1),
            ([-1, -4, -7], {0:8, 1:-2}, -7)
        ]

        for r, d, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.eval_factoid_rhs(d), res)

    def testEvalFactoidExcept(self):
        test_data = [
            ([2, 3, 4], {0:-1, 1:3}, 0, 13),
            ([2, 3, 4], {0:-1, 1:3}, 1, 2),
            ([2,-13,20,0,0], {0:0, 1:5, 2:-2, 3:100}, 2, -65)
        ]

        for r, d, j, res in test_data:
            f = Factoid(r)
            self.assertEqual(f.eval_factoid_except(d, j), res)

    def testNegateKey(self):
        test_data = [
            ([2,-5,4,3], (-2,5,-4,-3)),
            ([0,0,1], (0,0,-1))
        ]        

        for r, res in test_data:
            f = Factoid(r)
            f_res = Factoid(res)
            self.assertEqual(negate_key(f), f_res)

    def testCombineRealFactoid(self):
        test_data = [
            (1, [2, 3, -2], [5, -4, 7], [23, 0, 13]),
            (0, [3, -1, 6], [-2, 1, 3], [0, 1, 21])
        ]

        for i, r1, r2, res in test_data:
            r1, r2, res = Factoid(r1), Factoid(r2), Factoid(res)
            self.assertEqual(combine_real_factoid(i, r1, r2), res)

    def testCombineDarkFactoid(self):
        test_data = [
            (0, [2,3,4], [-3,-4,7], [0,1,24]),
            (1, [2,3,4], [-3,-4,7], [-1,0,31]),
        ]

        for i, r1, r2, res in test_data:
            r1, r2, res = Factoid(r1), Factoid(r2), Factoid(res)
            self.assertEqual(combine_dark_factoid(i, r1, r2), res)
    
    def testTermToFactoid(self):
        x = term.Var('x', IntType)
        y = term.Var('y', IntType)
        z = term.Var('z', IntType)
        vars = [x, y, z]

        test_data = [
            (term.less_eq(term.IntType)(term.Int(0), 3 * x + 2 * y + (-2)), (3,2,0,-2)),
            (term.less_eq(term.IntType)(term.Int(0),  1 * y), (0,1,0,0)),
            (term.less_eq(term.IntType)(term.Int(0), term.Number(IntType, 6)), (0,0,0,6))
        ]

        for r, res in test_data:
            self.assertEqual(term_to_factoid(vars, r), Factoid(res))

    def testLookUpFKey(self):
        db = dict()
        f1 = Factoid([3,-3,-2,1])
        f2 = Factoid([-4,2,1,2])
        f3 = Factoid([-3,3,2,-5])
        df1 = dfactoid(f1, NoConcl())
        df2 = dfactoid(f2, NoConcl())
        df3 = dfactoid(f3, NoConcl())

        for df in [df1, df2, df3]:
            insert_db(db, df)

        test_data = [
            ([3,-3,-2,5], (3,-3,-2)),
            ([-4,2,1,2], (-4,2,1))
        ]

        for r, res in test_data:
            r = Factoid(r)
            self.assertEqual(lookup_fkey(db, r).factoid.key, res)

    def testTopLevel(self):
        test_data = [
            ([[2,3,6],[-1,-4,7]], {0: -9, 1: 4}),
            ([[2,3,4],[-3,-4,7]], {0: 34, 1: -24}),
            ([[2,3,4],[-3,-4,7],[4,5,-10]], {1: -8, 0: 13}),
            ([[2,3,4],[-3,-4,7],[4,-5,-10]], {1: -1, 0: 2}),
            ([[1,0,-1], [0,1,-1], [-1,0,1]], {0: 1, 1: 1}),
            ([[1,2,3,4],[2,1,4,3],[5,6,7,-8],[-3,2,-1,6]], {0: 0, 1: 2, 2: 0}),
            ([[1,2,3,4],[2,-2,3,-10],[2,3,-5,6],[-3,-2,1,7]], {2: 2, 1: 0, 0: 2}),
            ([[-9, -11, -8, 9, 11], [15, 0, 8, -7, 8], [4, 3, 11, -2, -13]], {0: 8, 1: -6, 2: 0, 3: 0}),
            ([[-13, -8, -14, 15, 8], [-10, 9, 15, -13, 9], [-15, -14, -3, 2, 5]], {0: 0, 1: 0, 2: 0, 3: 0}),
            ([[2, -1, -5, 14, -7]], {0: 4, 1: 0, 2: 0, 3: 0})
        ]

        for matrix, sol in test_data:
            self.assertEqual(solve_matrix(matrix), ("SAT", sol))

    def testContradiction(self):
        test_data = [
            [(0, 1, 0, 1, 0, 1, 0, -1, 0, 0, 1), (0, -1, 0, -1, 0, 0, -1, 0, 0, 1, 1), 
            (0, -1, -1, 0, 0, 0, -1, 1, 1, 0, 0), (0, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0),
            (0, 0, 1, 0, -1, 0, -1, 0, 0, -1, -1), (-2, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0),
            (1, -1, 0, 1, 0, -1, -1, 0, 1, 0, 0), (0, -2, 0, 0, -1, 0, 0, 0, 0, 2, 0),
            (0, 0, 0, 0, 1, 0, 2, 1, 0, 0, -1), (1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0),
            (0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 1), (0, -1, 0, 0, 0, 0, -1, -2, -1, -1, 0),
            (0, 0, -1, -1, 0, -1, -1, 0, 1, 0, -1), (0, 0, -1, 1, 0, 1, 0, -1, 0, 0, -1),
            (0, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0), (-1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1),
            (1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1), (0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0),
            (1, 0, 0, 0, -3, 0, 0, 0, 0, 0, 1), (-1, 0, 1, 0, 0, -1, 1, 1, 0, 0, -1)],

            [(9, 0, 8, 0, 0, 2, 0, 0, -2, -6, 1), (4, 0, -4, -3, 7, 0, 0, -7, 8, -8, 4),
            (-8, 4, 0, 0, 1, 1, 0, -3, -7, 0, 2), (1, -5, 0, 0, 0, 3, 4, 0, -7, -7, 1),
            (3, 0, -8, 0, 0, 0, 0, -8, -4, 0, -9), (-2, -3, 0, 0, 5, 4, 0, 5, -9, -6, -8),
            (-17, 0, 5, 0, -1, 0, 0, 7, 0, 0, -6), (9, 0, 0, 8, 1, 12, 0, 0, 4, -8, -7),
            (0, -2, 0, -6, 0, 0, 0, -6, 8, -7, 7), (5, -4, 8, 0, 0, -8, 2, 0, -6, -3, 1),
            (0, 0, 2, 7, 0, -11, 2, 4, 0, 0, 9), (-2, -4, -3, 0, -6, -5, 0, 0, 5, -18, -3),
            (-2, -12, 0, 0, -2, -2, 0, -3, 5, 0, 8), (-3, 9, -7, 0, 0, 6, 5, -2, 4, -5, 0),
            (1, -1, 0, 0, 1, 7, 0, -7, 6, 9, 2), (5, 5, 4, 0, -9, 0, 2, 0, -13, 0, 1),
            (15, 0, -5, 5, 0, 2, 0, -6, 5, 0, -1), (0, 0, 0, 0, 0, 5, -3, 6, 0, 2, 0),
            (0, -5, 0, 0, -1, -3, 0, 9, -4, 0, 0), (-9, 6, 0, 0, 4, 0, -1, -3, -3, 0, 4)],            
        ]

        for f in test_data:
            status, _ = solve_matrix(f)
            assert status == "UNSAT"

    def testHOLRealCombine(self):
        test_data = [
            ([2, 1, -5], [-3, -1, 6], 1, 1, [-1, 0, 1]),
            ([1, -5, 0, 0, 0, 3, 4, 0, -7, -7, 1], [0, 0, 0, 0, 0, 5, -3, 6, 0, 2, 0], 
                        3, 4, [3, -15, 0, 0, 0, 29, 0, 24, -21, -13, 3])
        ]

        vars = term.IntVars('x0 x1 x2 x3 x4 x5 x6 x7 x8 x9')
        hol = OmegaHOL([])
        for first, second, m1, m2, res in test_data:
            hol = OmegaHOL([])
            len_fact = len(first)
            first, second = factoid_to_term(vars[:len_fact-1], first), factoid_to_term(vars[:len_fact - 1], second)
            after_combine = hol.real_combine_pt(proofterm.ProofTerm.assume(first), proofterm.ProofTerm.assume(second), m1, m2)
            after_combine_fact = term_to_factoid(vars[:len_fact-1], after_combine.prop)
            self.assertEqual(res, list(after_combine_fact.coeff))


    def testHOLGCD(self):
        test_data = [
            ([5, 0, -8], [1, 0, -2]),
            ([5, 0, 8], [1, 0, 1]),
            ([2, 4, 6, 5], [1, 2, 3, 2]),
            ([2, 4, 6, -5], [1, 2, 3, -3]),
        ]

        vars = term.IntVars('x0 x1 x2')
        hol = OmegaHOL([])
        for r, res in test_data:
            
            len_fact = len(r)
            r, res = factoid_to_term(vars[:len_fact-1], r), factoid_to_term(vars[:len_fact-1], res)
            after_gcd = hol.gcd_pt(vars[:len_fact-1], proofterm.ProofTerm.assume(r))
            self.assertEqual(res, after_gcd.prop)
