# Author: Bohua Zhan

import unittest

from kernel.macro import ProofMacro

def dummy_eval():
    raise NotImplementedError

def dummy_expand():
    raise NotImplementedError

class ProofMacroTest(unittest.TestCase):
    def testPrintMacro(self):
        macro = ProofMacro("test", dummy_eval)
        self.assertEqual(str(macro), "test (level 10, no expand)")

    def testPrintMacro2(self):
        macro = ProofMacro("test2", dummy_eval, dummy_expand, 5)
        self.assertEqual(str(macro), "test2 (level 5)")

    def testPrintMacro3(self):
        macro = ProofMacro("test3", None, dummy_expand, 5)
        self.assertEqual(str(macro), "test3 (level 5, no eval)")

if __name__ == "__main__":
    unittest.main()
