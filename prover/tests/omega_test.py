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
            (3 * x + 2 * y + (-2), (3,2,0,-2)),
            (1 * y, (0,1,0,0)),
            (term.Number(IntType, 6), (0,0,0,6))
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
            self.assertEqual(solve_matrix(matrix), sol)
