# Author: Bohua Zhan

import unittest
from kernel.type import *
from kernel.term import *
from kernel.thm import *
from kernel.extension import *

Ta = TVar("a")
x = Var("x", Ta)

class ExtensionTest(unittest.TestCase):
    def testConstantExtension(self):
        id_const = Const("id", TFun(Ta,Ta))
        id_def = Abs("x", Ta, Bound(0))
        ext = Extension.Constant("id", id_def)
        self.assertEqual(ext.get_const_term(), id_const)
        self.assertEqual(ext.get_eq_thm(), Thm([], Term.mk_equals(id_const, id_def)))

    def testPrintTheoryExtension(self):
        thy_ext = TheoryExtension()
        ext1 = Extension.Constant("id", Abs("x", Ta, Bound(0)))
        thy_ext.add_extension(ext1)
        
        id_const = ext1.get_const_term()
        id_simps = Term.mk_equals(Comb(id_const,x), x)
        thy_ext.add_extension(Extension.Theorem("id.simps", Thm([], id_simps)))

        str_thy_ext = "\n".join([
            "Constant id = Abs(x,'a,Bound 0)",
            "Theorem id.simps: |- equals (id x) x"])

        self.assertEqual(str(thy_ext), str_thy_ext)

if __name__ == "__main__":
    unittest.main()
