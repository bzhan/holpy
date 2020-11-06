# Author: Bohua Zhan

import unittest

from kernel import type as hol_type
from kernel.type import TVar, TFun
from kernel import term
from kernel.term import Term, Var, Const, Eq
from kernel.thm import Thm
from kernel.report import ProofReport, ExtensionReport
from syntax.settings import global_setting

Ta = TVar("a")
x = Var("x", Ta)

class ReportTest(unittest.TestCase):
    def setUp(self):
        self.type_printer, self.term_printer = hol_type.type_printer, term.term_printer
        hol_type.type_printer, term.term_printer = None, None

    def tearDown(self):
        hol_type.type_printer, term.term_printer = self.type_printer, self.term_printer

    def testStepCount(self):
        rpt = ProofReport()
        self.assertEqual(rpt.steps, 0)
        for i in range(10):
            rpt.apply_primitive_deriv()
        rpt.apply_theorem("th1")
        rpt.apply_theorem("th2")
        rpt.expand_macro("macro1")
        rpt.eval_macro("macro2")
        self.assertEqual(rpt.steps, 13)
        self.assertEqual(rpt.steps_stat(), (2, 10, 1))
        self.assertEqual(rpt.th_names, {"th1", "th2"})
        self.assertEqual(rpt.macros_expand, {"macro1"})
        self.assertEqual(rpt.macros_eval, {"macro2"})

    def testPrintExtensionReport(self):
        ext_report = ExtensionReport()

        id_const = Const("id", TFun(Ta,Ta))
        id_simps = Eq(id_const(x), x)
        ext_report.add_axiom("id.simps", Thm([], id_simps))

        str_ext_report = "\n".join([
            "Axiom added: 1",
            "id.simps: |- equals (id x) x"])

        with global_setting(unicode=False):
            self.assertEqual(str(ext_report), str_ext_report)

    def testPrintExtensionReport2(self):
        ext_report = ExtensionReport()
        ext_report.add_axiom("nat", 0)
        ext_report.add_axiom("id", TFun(Ta,Ta))

        str_ext_report = "\n".join([
            "Axiom added: 2",
            "Type nat with arity 0",
            "id :: 'a => 'a"])

        with global_setting(unicode=False):
            self.assertEqual(str(ext_report), str_ext_report)


if __name__ == "__main__":
    unittest.main()
