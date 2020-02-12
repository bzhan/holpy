import unittest

from kernel.type import BoolType
from kernel.term import Term, Var, Implies, And, Or
from kernel import report
from kernel import theory
from logic import basic
from prover import encode

a = Var('a', BoolType)
b = Var('b', BoolType)
c = Var('c', BoolType)
d = Var('d', BoolType)
e = Var('e', BoolType)


class EncodeTest(unittest.TestCase):
    def setUp(self):
        basic.load_theory('sat')

    def testLogicSubterms(self):
        t = Or(Implies(a,And(c,d)),Implies(b,And(c,e)))
        res = [
            a, b, c, d, e, And(c,d), And(c,e),
            Implies(a,And(c,d)), Implies(b,And(c,e)),
            Or(Implies(a,And(c,d)),Implies(b,And(c,e)))
        ]
        self.assertEqual(encode.logic_subterms(t), res)

    def testEncode(self):
        t = Or(Implies(a,And(c,d)),Implies(b,And(c,e)))
        pt = encode.tseitin_encode(t)
        self.assertEqual(len(pt.hyps), 11)
        self.assertEqual(len(pt.prop.strip_conj()), 16)
        
        rpt = report.ProofReport()
        self.assertEqual(theory.check_proof(pt.export(), rpt, check_level=1), pt.th)
        self.assertEqual(len(rpt.gaps), 0)

        cnf = encode.convert_cnf(pt.prop)
        self.assertEqual(len(cnf), 16)


if __name__ == "__main__":
    unittest.main()
