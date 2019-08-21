import unittest

from geometry.ruleset import ruleset

class RuleSetTest(unittest.TestCase):
    def testRuleSet(self):
        print(ruleset['D3'])


if __name__ == "__main__":
    unittest.main()
