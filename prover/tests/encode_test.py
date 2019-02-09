import unittest

from kernel.type import hol_bool
from kernel.term import Term, Var
from logic import logic
from syntax import printer
from prover import encode

conj = logic.mk_conj
disj = logic.mk_disj
neg = logic.neg
imp = Term.mk_implies
eq = Term.mk_equals
a = Var('a', hol_bool)
b = Var('b', hol_bool)
c = Var('c', hol_bool)
d = Var('d', hol_bool)
e = Var('e', hol_bool)


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
        cnf, prop = encode.encode(t)
        self.assertEqual(len(cnf), 16)
        self.assertEqual(len(prop.assums), 11)
        self.assertEqual(len(logic.strip_conj(prop.concl)), 16)

        pt = encode.get_encode_proof(prop)
        self.assertTrue(pt.th.can_prove(prop))

if __name__ == "__main__":
    unittest.main()
