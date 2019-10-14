# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun
from kernel.term import Term, Var, Const, Abs, Bound
from kernel.thm import Thm
from kernel.extension import Type, Constant, Theorem, TheoryExtension


class ExtensionTest(unittest.TestCase):
    def testPrintTheoryExtension(self):
        thy_ext = TheoryExtension()
        thy_ext.add_extension(Type("nat", 0))
        thy_ext.add_extension(Constant("id", TFun(TVar("a"),TVar("a"))))

        str_thy_ext = "\n".join([
            "Type nat 0",
            "Constant id :: 'a => 'a"])

        self.assertEqual(str(thy_ext), str_thy_ext)


if __name__ == "__main__":
    unittest.main()
