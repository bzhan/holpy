# Author: Bohua Zhan

import unittest
from kernel.type import TVar, TFun
from kernel.term import Term, Var, Const
from kernel.thm import Thm
from kernel.report import ProofReport, ExtensionReport

Ta = TVar("a")
x = Var("x", Ta)

class ProofReportTest(unittest.TestCase):
    def testStepCount(self):
        rpt = ProofReport()
        self.assertEqual(rpt.steps, 0)
        for i in range(10):
            rpt.apply_base_deriv()
        rpt.apply_theorem("th1")
        rpt.apply_theorem("th2")
        rpt.expand_macro("macro1")
        rpt.eval_macro("macro2")
        self.assertEqual(rpt.steps, 13)
        self.assertEqual(rpt.steps_stat(), (2, 10, 1))
        self.assertEqual(rpt.th_names, {"th1", "th2"})
        self.assertEqual(rpt.macros_expand, {"macro1"})
        self.assertEqual(rpt.macros_eval, {"macro2"})

class ExtensionReportTest(unittest.TestCase):
    def testPrintExtensionReport(self):
        ext_report = ExtensionReport()

        id_const = Const("id", TFun(Ta,Ta))
        id_simps = Term.mk_equals(id_const(x), x)
        ext_report.add_axiom("id.simps", Thm([], id_simps))

        str_ext_report = "\n".join([
            "Axiom added: 1",
            "id.simps: |- equals (id x) x"])

        self.assertEqual(str(ext_report), str_ext_report)

    def testPrintExtensionReport2(self):
        ext_report = ExtensionReport()
        ext_report.add_axiom("id", TFun(Ta,Ta))

        str_ext_report = "\n".join([
            "Axiom added: 1",
            "id :: 'a => 'a"])

        self.assertEqual(str(ext_report), str_ext_report)

if __name__ == "__main__":
    unittest.main()
