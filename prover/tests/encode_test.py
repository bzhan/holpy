import unittest

from kernel.type import boolT
from kernel.term import Term, Var
from kernel import report
from logic import logic
from logic import basic
from syntax import printer
from prover import encode

conj = logic.mk_conj
disj = logic.mk_disj
neg = logic.neg
imp = Term.mk_implies
eq = Term.mk_equals
a = Var('a', boolT)
b = Var('b', boolT)
c = Var('c', boolT)
d = Var('d', boolT)
e = Var('e', boolT)


class EncodeTest(unittest.TestCase):
    def testLogicSubterms(self):
        t = disj(imp(a,conj(c,d)),imp(b,conj(c,e)))
        res = [
            a, c, d, conj(c,d), imp(a,conj(c,d)),
            b, c, e, conj(c,e), imp(b,conj(c,e)),
            disj(imp(a,conj(c,d)),imp(b,conj(c,e)))
        ]
        self.assertEqual(encode.logic_subterms(t), res)

    def testEncode(self):
        t = disj(imp(a,conj(c,d)),imp(b,conj(c,e)))
        cnf, th = encode.encode(t)
        self.assertEqual(len(cnf), 16)
        self.assertEqual(len(th.hyps), 11)
        self.assertEqual(len(logic.strip_conj(th.prop)), 16)

        pt = encode.get_encode_proof(th)
        self.assertEqual(pt.th, th)
        
        thy = basic.load_theory('sat')
        rpt = report.ProofReport()
        self.assertEqual(thy.check_proof(pt.export(), rpt, check_level=1), pt.th)
        self.assertEqual(len(rpt.gaps), 0)


if __name__ == "__main__":
    unittest.main()
