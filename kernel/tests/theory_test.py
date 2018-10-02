# Author: Bohua Zhan

import unittest
from kernel.thm import *
from kernel.proof import *
from kernel.macro import *
from kernel.theory import *

thy = Theory.EmptyTheory()

Ta = TVar("a")
Tb = TVar("b")
Tab = TFun(Ta, Tb)
x = Var("x", Ta)
y = Var("y", Ta)
z = Var("z", Ta)
f = Var("f", Tab)
A = Var("A", hol_bool)
B = Var("B", hol_bool)
C = Var("C", hol_bool)

# A simple macro
def beta_conv_rhs_eval(th):
    assert Term.is_equals(th.concl), "beta_conv_rhs"
    (_, rhs) = th.concl.dest_binop()

    return Thm.transitive(th, Thm.beta_conv(rhs))

def beta_conv_rhs_expand(id, ids, th):
    assert Term.is_equals(th.concl), "beta_conv_rhs"
    (_, rhs) = th.concl.dest_binop()

    th1 = Thm.beta_conv(rhs)
    th2 = Thm.transitive(th, th1)
    prf = [
        ProofItem(id + ".S1", th1, "beta_conv", rhs, []),
        ProofItem("C", th2, "transitive", [], [ids[0], id + ".S1"])]
    return prf

beta_conv_rhs_macro = ProofMacro(
    "Reduce the right side of th by beta-conversion.",
    beta_conv_rhs_eval,
    beta_conv_rhs_expand
)

class TheoryTest(unittest.TestCase):
    def testEmptyTheory(self):
        self.assertEqual(thy.get_type_sig("bool"), 0)
        self.assertEqual(thy.get_type_sig("fun"), 2)
        self.assertEqual(thy.get_term_sig("equals"), TFun(Ta,TFun(Ta,hol_bool)))
        self.assertEqual(thy.get_term_sig("implies"), TFun(hol_bool,TFun(hol_bool,hol_bool)))

    def testCheckType(self):
        test_data = [
            Ta,
            TFun(Ta, Tb),
            TFun(TFun(Ta, Ta), Tb),
            TFun(hol_bool, hol_bool),
            TFun(TFun(Ta, hol_bool), hol_bool),
        ]

        for T in test_data:
            self.assertEqual(thy.check_type(T), None)

    def testCheckTypeFail(self):
        test_data = [
            Type("bool", Ta),
            Type("bool", [Ta, Ta]),
            Type("fun"),
            Type("fun", Ta),
            Type("fun", [Ta, Ta, Ta]),
            Type("random")
        ]

        for T in test_data:
            self.assertRaises(TheoryException, thy.check_type, T)

    def testCheckTerm(self):
        test_data = [
            x,
            Term.mk_equals(x, y),
            Term.mk_equals(f, f),
            Term.mk_implies(A, B),
            Abs("x", Ta, Term.mk_equals(x, y)),
        ]

        for t in test_data:
            self.assertEqual(thy.check_term(t), None)

    def testCheckTermFail(self):
        test_data = [
            Const("random", Ta),
            Const("equals", TFun(Ta, TFun(Tb, hol_bool))),
            Const("equals", TFun(Ta, TFun(Ta, Tb))),
            Const("implies", TFun(Ta, TFun(Ta, hol_bool))),
            Comb(Const("random", Tab), x),
            Comb(f, Const("random", Ta)),
            Abs("x", Ta, Const("random", Ta)),
        ]

        for t in test_data:
            self.assertRaises(TheoryException, thy.check_term, t)

    def testCheckProof(self):
        """Proof of [A, A --> B] |- B."""
        A_to_B = Term.mk_implies(A, B)
        th = Thm([A, A_to_B], B)
        prf = Proof(A_to_B, A)
        prf.add_item("C", th, "implies_elim", None, ["A1", "A2"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProof2(self):
        """Proof of |- A --> A."""
        th = Thm([], Term.mk_implies(A,A))
        prf = Proof(A)
        prf.add_item("C", th, "implies_intr", A, ["A1"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProof3(self):
        """Proof of [x = y, y = z] |- f z = f x."""
        x_eq_y = Term.mk_equals(x,y)
        y_eq_z = Term.mk_equals(y,z)
        th = Thm([x_eq_y, y_eq_z], Term.mk_equals(Comb(f,z), Comb(f,x)))
        prf = Proof(x_eq_y, y_eq_z)
        prf.add_item("S1", Thm([x_eq_y, y_eq_z], Term.mk_equals(x,z)), "transitive", None, ["A1", "A2"])
        prf.add_item("S2", Thm([x_eq_y, y_eq_z], Term.mk_equals(z,x)), "symmetric", None, ["S1"])
        prf.add_item("S3", Thm([], Term.mk_equals(f,f)), "reflexive", f, None)
        prf.add_item("C", th, "combination", None, ["S3", "S2"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProof4(self):
        """Proof of |- x = y --> x = y by instantiating an existing theorem."""
        thy = Theory.EmptyTheory()
        thy.add_theorem("trivial", Thm([], Term.mk_implies(A,A)))

        x_eq_y = Term.mk_equals(x,y)
        th = Thm([], Term.mk_implies(x_eq_y,x_eq_y))
        prf = Proof()
        prf.add_item("S1", Thm([], Term.mk_implies(A,A)), "theorem", "trivial", [])
        prf.add_item("C", th, "substitution", {"A" : x_eq_y}, ["S1"])

        self.assertEqual(thy.check_proof(prf), th)

    def testCheckProofFail(self):
        """Previous item not found."""
        prf = Proof()
        prf.add_item("C", Thm([], A), "implies_intr", None, ["A1"])

        self.assertRaisesRegex(CheckProofException, "previous item not found", thy.check_proof, prf)

    def testCheckProofFail2(self):
        """Invalid derivation."""
        prf = Proof(A)
        prf.add_item("C", Thm([A], A), "symmetric", None, ["A1"])

        self.assertRaisesRegex(CheckProofException, "invalid derivation", thy.check_proof, prf)

    def testCheckProofFail3(self):
        """Invalid input to derivation."""
        prf = Proof(A)
        prf.add_item("C", Thm([], Term.mk_implies(A,A)), "implies_intr", None, ["A1"])

        self.assertRaisesRegex(CheckProofException, "invalid input to derivation", thy.check_proof, prf)

    def testCheckProofFail4(self):
        """Output does not match."""
        prf = Proof(A)
        prf.add_item("C", Thm([], Term.mk_implies(A,B)), "implies_intr", A, ["A1"])

        self.assertRaisesRegex(CheckProofException, "output does not match", thy.check_proof, prf)

    def testCheckProofFail5(self):
        """Theorem not found."""
        prf = Proof()
        prf.add_item("C", Thm([], Term.mk_implies(A,B)), "theorem", "random", None)

        self.assertRaisesRegex(CheckProofException, "theorem not found", thy.check_proof, prf)

    def testCheckProofFail6(self):
        """Typing error: statement is not non-boolean."""
        prf = Proof(x)

        self.assertRaisesRegex(CheckProofException, "typing error", thy.check_proof, prf)

    def testCheckProofFail7(self):
        """Typing error: type-checking failed."""
        prf = Proof(Comb(Var("P", TFun(Tb, hol_bool)), x))

        self.assertRaisesRegex(CheckProofException, "typing error", thy.check_proof, prf)

    def testCheckProofFail8(self):
        """Proof method not found."""
        prf = Proof()
        prf.add_item("C", Thm([], Term.mk_implies(A,B)), "random", None, None)

        self.assertRaisesRegex(CheckProofException, "proof method not found", thy.check_proof, prf)

    def testCheckProofMacro(self):
        """Proof checking with simple macro."""
        thy = Theory.EmptyTheory()
        thy.add_proof_macro("beta_conv_rhs", beta_conv_rhs_macro)
        
        t = Comb(Abs("x", Ta, Bound(0)), x)
        th = Thm([], Term.mk_equals(t,x))

        prf = Proof()
        prf.add_item("S1", Thm([], Term.mk_equals(t,t)), "reflexive", t, [])
        prf.add_item("C", th, "beta_conv_rhs", None, ["S1"])

        self.assertEqual(thy.check_proof(prf), th)

    def testUncheckedExtend(self):
        """Unchecked extension."""
        thy = Theory.EmptyTheory()
        thy_ext = TheoryExtension()

        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        id_simps = Term.mk_equals(Comb(id_const,x), x)

        thy_ext.add_extension(Extension.Constant("id", id_def))        
        thy_ext.add_extension(Extension.Theorem("id.simps", Thm([], id_simps)))

        self.assertEqual(thy.unchecked_extend(thy_ext), None)
        self.assertEqual(thy.get_term_sig("id"), TFun(Ta, Ta))
        self.assertEqual(thy.get_theorem("id_def"), Thm([], Term.mk_equals(id_const, id_def)))
        self.assertEqual(thy.get_theorem("id.simps"), Thm([], id_simps))

    def testCheckedExtend(self):
        """Checked extension: adding an axiom."""
        thy = Theory.EmptyTheory()
        thy_ext = TheoryExtension()

        id_simps = Term.mk_equals(Comb(Const("id", TFun(Ta,Ta)),x), x)
        thy_ext.add_extension(Extension.Theorem("id.simps", Thm([], id_simps)))

        ext_report = thy.checked_extend(thy_ext)
        self.assertEqual(thy.get_theorem("id.simps"), Thm([], id_simps))
        self.assertEqual(ext_report.get_axioms(), [("id.simps", Thm([], id_simps))])

    def testCheckedExtend2(self):
        """Checked extension: proved theorem."""
        thy = Theory.EmptyTheory()
        thy_ext = TheoryExtension()

        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        id_simps = Term.mk_equals(Comb(id_const,x), x)

        # Proof of |- id x = x from |- id = (%x. x)
        prf = Proof()
        th1 = Thm([], Term.mk_equals(id_const, id_def))  # id = (%x. x)
        th2 = Thm.reflexive(x)  # x = x
        th3 = Thm.combination(th1, th2)  # id x = (%x. x) x
        th4 = Thm.beta_conv(Comb(id_def, x))  # (%x. x) x = x
        th5 = Thm.transitive(th3, th4)  # id x = x
        prf.add_item("S1", th1, "theorem", "id_def", None)
        prf.add_item("S2", th2, "reflexive", x, None)
        prf.add_item("S3", th3, "combination", None, ["S1", "S2"])
        prf.add_item("S4", th4, "beta_conv", Comb(id_def, x), None)
        prf.add_item("C", th5, "transitive", None, ["S3", "S4"])

        thy_ext.add_extension(Extension.Constant("id", id_def))
        thy_ext.add_extension(Extension.Theorem("id.simps", th5, prf))

        ext_report = thy.checked_extend(thy_ext)
        self.assertEqual(thy.get_theorem("id.simps"), Thm([], id_simps))
        self.assertEqual(ext_report.get_axioms(), [])

    def testCheckedExtend3(self):
        """Axiomatized constant."""
        thy = Theory.EmptyTheory()
        thy_ext = TheoryExtension()

        thy_ext.add_extension(Extension.AxConstant("id", TFun(Ta,Ta)))
        ext_report = thy.checked_extend(thy_ext)
        self.assertEqual(thy.get_term_sig("id"), TFun(Ta,Ta))
        self.assertEqual(ext_report.get_axioms(), [("id", TFun(Ta,Ta))])

if __name__ == "__main__":
    unittest.main()
