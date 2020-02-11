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
            a, c, d, And(c,d), Implies(a,And(c,d)),
            b, c, e, And(c,e), Implies(b,And(c,e)),
            Or(Implies(a,And(c,d)),Implies(b,And(c,e)))
        ]
        self.assertEqual(encode.logic_subterms(t), res)

    def testEncode(self):
        t = Or(Implies(a,And(c,d)),Implies(b,And(c,e)))
        cnf, hyps, th = encode.encode(t)
        self.assertEqual(len(cnf), 16)
        self.assertEqual(len(th.hyps), 11)
        self.assertEqual(len(th.prop.strip_conj()), 16)

        pt = encode.get_encode_proof(hyps, th)
        self.assertEqual(pt.th, th)
        
        rpt = report.ProofReport()
        self.assertEqual(theory.check_proof(pt.export(), rpt, check_level=1), pt.th)
        self.assertEqual(len(rpt.gaps), 0)


if __name__ == "__main__":
    unittest.main()
