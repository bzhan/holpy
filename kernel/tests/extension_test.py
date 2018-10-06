# Author: Bohua Zhan

import unittest
from kernel.type import TVar, TFun
from kernel.term import Term, Var, Const, Abs, Bound
from kernel.thm import Thm
from kernel.extension import AxConstant, Constant, Theorem, TheoryExtension

Ta = TVar("a")
x = Var("x", Ta)

class ExtensionTest(unittest.TestCase):
    def testConstantExtension(self):
        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        ext = Constant("id", id_def)
        self.assertEqual(ext.get_const_term(), id_const)
        self.assertEqual(ext.get_eq_thm(), Thm.mk_equals(id_const, id_def))

    def testPrintTheoryExtension(self):
        thy_ext = TheoryExtension()

        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        id_simps = Term.mk_equals(id_const(x), x)
        
        thy_ext.add_extension(Constant("id", id_def))
        thy_ext.add_extension(Theorem("id.simps", Thm([], id_simps)))

        str_thy_ext = "\n".join([
            "Constant id = Abs(x,'a,Bound 0)",
            "Theorem id.simps: |- equals (id x) x"])

        self.assertEqual(str(thy_ext), str_thy_ext)

    def testPrintTheoryExtension2(self):
        thy_ext = TheoryExtension()
        thy_ext.add_extension(AxConstant("id", TFun(Ta,Ta)))
        
        self.assertEqual(str(thy_ext), "AxConstant id :: 'a => 'a")

if __name__ == "__main__":
    unittest.main()
