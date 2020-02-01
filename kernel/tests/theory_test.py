# Author: Bohua Zhan

import unittest

from kernel.type import Type, TVar, TFun, boolT
from kernel.term import Term, SVar, Var, Const, Comb, Abs, Bound, Implies, Eq
from kernel.thm import Thm
from kernel.proof import Proof, ItemID
from kernel.macro import ProofMacro
from kernel import theory
from kernel.theory import Theory, TheoryException, CheckProofException
from kernel import extension
from kernel.report import ProofReport, ExtensionReport


Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", Tab)
A = Var("A", boolT)
B = Var("B", boolT)
C = Var("C", boolT)

# A simple macro
class beta_conv_rhs_macro(ProofMacro):
    """Reduce the right side of th by beta-conversion."""
    def __init__(self):
        self.level = 1
        self.sig = Term

    def eval(self, args, ths):
        th = ths[0]
        assert th.prop.is_equals(), "beta_conv_rhs"
        rhs = th.prop.rhs

        return Thm.transitive(th, Thm.beta_conv(rhs))

    def expand(self, prefix, args, prevs):
        id, th = prevs[0]
        assert th.prop.is_equals(), "beta_conv_rhs"
        rhs = th.prop.rhs

        prf = Proof()
        prf.add_item(ItemID(prefix.id + (0,)), "beta_conv", args=rhs)
        prf.add_item(ItemID(prefix.id + (1,)), "transitive", prevs=[id, ItemID(prefix.id + (0,))])
        return prf


class TheoryTest(unittest.TestCase):
    def setUp(self):
        theory.thy = theory.EmptyTheory()

    def testEmptyTheory(self):
        self.assertEqual(theory.thy.get_type_sig("bool"), 0)
        self.assertEqual(theory.thy.get_type_sig("fun"), 2)
        self.assertEqual(theory.thy.get_term_sig("equals"), TFun(Ta,Ta,boolT))
        self.assertEqual(theory.thy.get_term_sig("implies"), TFun(boolT,boolT,boolT))

    def testCheckType(self):
        test_data = [
            Ta,
            TFun(Ta, Tb),
            TFun(TFun(Ta, Ta), Tb),
            TFun(boolT, boolT),
            TFun(TFun(Ta, boolT), boolT),
        ]

        for T in test_data:
            self.assertEqual(theory.thy.check_type(T), None)

    def testCheckTypeFail(self):
        test_data = [
            Type("bool", Ta),
            Type("bool", Ta, Ta),
            Type("fun"),
            Type("fun", Ta),
            Type("fun", Ta, Ta, Ta),
            TFun(Type("bool", Ta), Type("bool")),
            TFun(Type("bool"), Type("bool", Ta)),
            Type("random")
        ]

        for T in test_data:
            self.assertRaises(TheoryException, theory.thy.check_type, T)

    def testCheckTerm(self):
        test_data = [
            x,
            Eq(x, y),
            Eq(f, f),
            Implies(A, B),
            Abs("x", Ta, Eq(x, y)),
        ]

        for t in test_data:
            self.assertEqual(theory.thy.check_term(t), None)

    def testCheckTermFail(self):
        test_data = [
            Const("random", Ta),
            Const("equals", TFun(Ta, Tb, boolT)),
            Const("equals", TFun(Ta, Ta, Tb)),
            Const("implies", TFun(Ta, Ta, boolT)),
            Comb(Const("random", Tab), x),
            f(Const("random", Ta)),
            Abs("x", Ta, Const("random", Ta)),
        ]

        for t in test_data:
            self.assertRaises(TheoryException, theory.thy.check_term, t)

    def testCheckProof(self):
        """Proof of [A, A --> B] |- B."""
        A_to_B = Implies(A, B)
        prf = Proof(A_to_B, A)
        prf.add_item(2, "implies_elim", prevs=[0, 1])

        rpt = ProofReport()
        self.assertEqual(theory.thy.check_proof(prf, rpt), Thm([A_to_B, A], B))
        self.assertEqual(rpt.steps, 3)

    def testCheckProof2(self):
        """Proof of |- A --> A."""
        prf = Proof(A)
        prf.add_item(1, "implies_intr", args=A, prevs=[0])

        rpt = ProofReport()
        self.assertEqual(theory.thy.check_proof(prf, rpt), Thm([], Implies(A,A)))
        self.assertEqual(rpt.steps, 2)

    def testCheckProof3(self):
        """Proof of [x = y, y = z] |- f z = f x."""
        x_eq_y = Eq(x,y)
        y_eq_z = Eq(y,z)
        prf = Proof(x_eq_y, y_eq_z)
        prf.add_item(2, "transitive", prevs=[0, 1])
        prf.add_item(3, "symmetric", prevs=[2])
        prf.add_item(4, "reflexive", args=f)
        prf.add_item(5, "combination", prevs=[4, 3])

        rpt = ProofReport()
        th = Thm([x_eq_y, y_eq_z], Eq(f(z),f(x)))
        self.assertEqual(theory.thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.steps, 6)

    def testCheckProof4(self):
        """Proof of |- x = y --> x = y by instantiating an existing theorem."""
        theory.thy.add_theorem("trivial", Thm([], Implies(A,A)))

        x_eq_y = Eq(x,y)
        prf = Proof()
        prf.add_item(0, "theorem", args="trivial")
        prf.add_item(1, "substitution", args={"A" : x_eq_y}, prevs=[0])

        rpt = ProofReport()
        th = Thm([], Implies(x_eq_y,x_eq_y))
        self.assertEqual(theory.thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.steps, 2)

    def testCheckProof5(self):
        """Empty instantiation."""
        theory.thy.add_theorem("trivial", Thm([], Implies(A,A)))

        x_eq_y = Eq(x,y)
        prf = Proof()
        prf.add_item(0, "theorem", args="trivial")
        prf.add_item(1, "substitution", args={}, prevs=[0])

        rpt = ProofReport()
        th = Thm([], Implies(SVar('A', boolT), SVar('A', boolT)))
        self.assertEqual(theory.thy.check_proof(prf, rpt), th)
        self.assertEqual(rpt.steps_stat(), (1, 1, 0))
        self.assertEqual(rpt.th_names, {"trivial"})

    def testCheckProofFail(self):
        """Previous item not found."""
        prf = Proof()
        prf.add_item(0, "implies_intr", prevs=[1])

        self.assertRaisesRegex(CheckProofException, "id 0 cannot depend on 1", theory.thy.check_proof, prf)

    def testCheckProofFail2(self):
        """Invalid derivation."""
        prf = Proof(A)
        prf.add_item(1, "symmetric", prevs=[0])

        self.assertRaisesRegex(CheckProofException, "invalid derivation", theory.thy.check_proof, prf)

    def testCheckProofFail3(self):
        """Invalid input to derivation."""
        prf = Proof(A)
        prf.add_item(1, "implies_intr", prevs=[0])

        self.assertRaisesRegex(CheckProofException, "invalid input to derivation", theory.thy.check_proof, prf)

    def testCheckProofFail4(self):
        """Output does not match."""
        prf = Proof(A)
        prf.add_item(1, "implies_intr", args=A, prevs=[0], th = Thm([], Implies(A,B)))

        self.assertRaisesRegex(CheckProofException, "output does not match", theory.thy.check_proof, prf)

    def testCheckProofFail5(self):
        """Theorem not found."""
        prf = Proof()
        prf.add_item(0, "theorem", args="random")

        self.assertRaisesRegex(CheckProofException, "theorem not found", theory.thy.check_proof, prf)

    def testCheckProofFail6(self):
        """Typing error: statement is not non-boolean."""
        prf = Proof(x)

        self.assertRaisesRegex(CheckProofException, "typing error", theory.thy.check_proof, prf)

    def testCheckProofFail7(self):
        """Typing error: type-checking failed."""
        prf = Proof(Comb(Var("P", TFun(Tb, boolT)), x))

        self.assertRaisesRegex(CheckProofException, "typing error", theory.thy.check_proof, prf)

    def testCheckProofFail8(self):
        """Proof method not found."""
        prf = Proof()
        prf.add_item(0, "random")

        self.assertRaisesRegex(CheckProofException, "proof method not found", theory.thy.check_proof, prf)

    def testAssumsSubset(self):
        """res_th is OK if assumptions is a subset of that of seq.th."""
        prf = Proof()
        prf.add_item(0, "assume", args=A, th=Thm([A, B], A))

        self.assertEqual(theory.thy.check_proof(prf), Thm([A, B], A))

    def testAssumsSubsetFail(self):
        """res_th is not OK if assumptions is not a subset of that of seq.th."""
        prf = Proof()
        prf.add_item(0, "assume", args=A, th=Thm([], A))

        self.assertRaisesRegex(CheckProofException, "output does not match", theory.thy.check_proof, prf)

    def testCheckProofGap(self):
        """Check proof with gap."""
        prf = Proof()
        prf.add_item(0, "sorry", th = Thm([], Implies(A,B)))
        prf.add_item(1, "sorry", th = Thm([], A))
        prf.add_item(2, "implies_elim", prevs=[0, 1])

        rpt = ProofReport()
        self.assertEqual(theory.thy.check_proof(prf, rpt), Thm([], B))
        self.assertEqual(rpt.gaps, [Thm([], Implies(A, B)), Thm([], A)])

    def testUncheckedExtend(self):
        """Unchecked extension."""
        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))

        exts = [
            extension.Constant("id", TFun(Ta, Ta)),
            extension.Theorem("id_def", Thm([], Eq(id_const, id_def))),
            extension.Theorem("id.simps", Thm([], Eq(id_const, x)))
        ]

        self.assertEqual(theory.thy.unchecked_extend(exts), None)
        self.assertEqual(theory.thy.get_term_sig("id"), TFun(Ta, Ta))
        self.assertEqual(theory.thy.get_theorem("id_def"), Thm([], Eq(id_const, id_def)))
        self.assertEqual(theory.thy.get_theorem("id.simps"), Thm([], Eq(id_const, x)))

    def testCheckedExtend(self):
        """Checked extension: adding an axiom."""
        id_simps = Eq(Comb(Const("id", TFun(Ta,Ta)),x), x)
        exts = [extension.Theorem("id.simps", Thm([], id_simps))]

        ext_report = theory.thy.checked_extend(exts)
        self.assertEqual(theory.thy.get_theorem("id.simps"), Thm([], id_simps))
        self.assertEqual(ext_report.get_axioms(), [("id.simps", Thm([], id_simps))])

    def testCheckedExtend2(self):
        """Checked extension: proved theorem."""
        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        id_simps = Eq(id_const(x), x)

        # Proof of |- id x = x from |- id = (%x. x)
        prf = Proof()
        prf.add_item(0, "theorem", args="id_def")  # id = (%x. x)
        prf.add_item(1, "subst_type", args={'a': TVar('a')}, prevs=[0])  # id = (%x. x)
        prf.add_item(2, "reflexive", args=x)  # x = x
        prf.add_item(3, "combination", prevs=[1, 2])  # id x = (%x. x) x
        prf.add_item(4, "beta_conv", args=id_def(x))  # (%x. x) x = x
        prf.add_item(5, "transitive", prevs=[3, 4])  # id x = x

        exts = [
            extension.Constant("id", TFun(Ta, Ta)),
            extension.Theorem("id_def", Thm([], Eq(id_const, id_def))),
            extension.Theorem("id.simps", Thm([], id_simps), prf)
        ]

        ext_report = theory.thy.checked_extend(exts)
        self.assertEqual(theory.thy.get_theorem("id.simps"), Thm([], id_simps))
        self.assertEqual(ext_report.get_axioms(), [('id_def', Thm([], Eq(id_const, id_def)))])

    def testCheckedExtend3(self):
        """Axiomatized constant."""
        exts = [
            extension.Type("nat", 0),
            extension.Constant("id", TFun(Ta,Ta))
        ]
        ext_report = theory.thy.checked_extend(exts)
        self.assertEqual(theory.thy.get_type_sig("nat"), 0)
        self.assertEqual(theory.thy.get_term_sig("id"), TFun(Ta,Ta))


if __name__ == "__main__":
    unittest.main()
