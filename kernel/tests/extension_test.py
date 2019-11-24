# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun
from kernel.term import Term, Var, Const, Abs, Bound
from kernel.thm import Thm
from kernel.extension import Type, Constant, Theorem


class ExtensionTest(unittest.TestCase):
    def testPrintExtension(self):
        exts = [
            Type("nat", 0),
            Constant("id", TFun(TVar("a"),TVar("a")))
        ]

        str_exts = [
            "Type nat 0",
            "Constant id :: 'a => 'a"
        ]

        for ext, str_ext in zip(exts, str_exts):
            self.assertEqual(str(ext), str_ext)


if __name__ == "__main__":
    unittest.main()
