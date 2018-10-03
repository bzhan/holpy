# Author: Bohua Zhan

import unittest
from kernel.type import *
from kernel.term import *
from kernel.thm import *
from kernel.report import *

Ta = TVar("a")
x = Var("x", Ta)

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
