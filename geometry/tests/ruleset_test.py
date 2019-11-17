import unittest

from geometry.ruleset import ruleset

class RuleSetTest(unittest.TestCase):
    def testRuleSet(self):
        self.assertEqual(str(ruleset['D5']), 'para(m,l) :- para(l,m)')


if __name__ == "__main__":
    unittest.main()
