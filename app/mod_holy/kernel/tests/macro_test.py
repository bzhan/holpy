# Author: Bohua Zhan

import unittest

from kernel.macro import ProofMacro

class TestMacro1(ProofMacro):
    def __init__(self):
        self.level = 10

    def __call__(self):
        pass

class TestMacro2(ProofMacro):
    def __init__(self):
        self.level = 5

    def __call__(self):
        pass

    def expand(self):
        pass

class TestMacro3(ProofMacro):
    def __init__(self):
        self.level = 5

    def expand(self):
        pass

class ProofMacroTest(unittest.TestCase):
    def testPrintMacro(self):
        macro = TestMacro1()
        self.assertEqual(str(macro), "level 10, no expand")

    def testPrintMacro2(self):
        macro = TestMacro2()
        self.assertEqual(str(macro), "level 5")

    def testPrintMacro3(self):
        macro = TestMacro3()
        self.assertEqual(str(macro), "level 5, no eval")

if __name__ == "__main__":
    unittest.main()
