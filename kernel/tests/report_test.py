# Author: Bohua Zhan

import unittest
from kernel.type import TVar, TFun
from kernel.term import Term, Var, Const, Comb
from kernel.thm import Thm
from kernel.report import ProofReport, ExtensionReport

Ta = TVar("a")
x = Var("x", Ta)

class ProofReportTest(unittest.TestCase):
    def testStepCount(self):
        rpt = ProofReport()
        self.assertEqual(rpt.count_steps, True)
        self.assertEqual(rpt.get_step_count(), 0)
        rpt.incr_step_count()
        self.assertEqual(rpt.get_step_count(), 1)
        rpt.count_steps = False
        rpt.incr_step_count()
        self.assertEqual(rpt.get_step_count(), 1)

class ExtensionReportTest(unittest.TestCase):
    def testPrintExtensionReport(self):
        ext_report = ExtensionReport()

        id_const = Const("id", TFun(Ta,Ta))
        id_simps = Term.mk_equals(Comb(id_const,x), x)
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
