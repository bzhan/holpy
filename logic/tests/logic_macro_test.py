# Author: Chengwei Zhang

import unittest

from kernel.type import boolT
from kernel.term import Term, Var
from kernel.thm import Thm, InvalidDerivationException
from logic import logic
from logic.logic_macro import imp_conj_macro, trivial_macro
from logic import basic
from syntax import printer

thy = basic.load_theory('logic_base')

imp = Term.mk_implies
conj = logic.mk_conj


class LogicMacroTest(unittest.TestCase):
    def testTrivialMacro(self):
        macro = trivial_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        test_data = [
            imp(A, A),
            imp(A, B, A),
            imp(A, A, B, A),
        ]

        for t in test_data:
            pt = macro.get_proof_term(thy, t, [])
            prf = pt.export()
            self.assertEqual(thy.check_proof(prf), Thm([], t))

    def testImpConjMacro(self):
        macro = imp_conj_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        C = Var("C", boolT)
        D = Var("D", boolT)
        test_data = [
            (imp(conj(conj(A, conj(D, B), C)), conj(conj(A, D, C), conj(A, B))), True),
            (imp(conj(C, D), A), False),
            (imp(conj(A, B), conj(A, conj(B, C))), False),
            (imp(conj(A, conj(B, C)), conj(A, B)), True),
        ]

        for t, res in test_data:
            if res:
                pt = macro.get_proof_term(thy, t, [])
                self.assertEqual(pt, Thm([], t))
                prf = pt.export()
                thy.check_proof(prf)
            else:
                self.assertRaises(AssertionError, macro.get_proof_term, thy, t, [])

    def testImpConjMacroEval(self):
        macro = imp_conj_macro()
        A = Var("A", boolT)
        B = Var("B", boolT)
        C = Var("C", boolT)
        D = Var("D", boolT)
        test_data = [
            (imp(conj(conj(A, conj(D, B))), conj(conj(A, D), conj(B, A))), True),
            (imp(B, C), False),
            (imp(conj(A, B), conj(A, conj(B, C))), False),
            (imp(conj(A, conj(B, C)), conj(A, B)), True),
        ]

        for t, res in test_data:
            if res:
                self.assertEqual(macro.eval(thy, t, []), Thm([], t))
            else:
                self.assertRaises(AssertionError, macro.eval, thy, t, [])


if __name__ == "__main__":
    unittest.main()
