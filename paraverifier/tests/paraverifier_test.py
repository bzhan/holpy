# Author: Bohua Zhan

import unittest

from kernel.type import TFun, boolT
from kernel.term import Term, Var, Const
from logic import basic
from data.nat import natT
from logic.logic import true, false, neg, mk_conj
from syntax import printer
from paraverifier import gcl
from paraverifier.paraverifier import load_system, load_hints

print_log = False
def log(*s):
    if print_log:
        print(*s)


class ParaverifierTest(unittest.TestCase):
    def testMutualEx(self):
        sys = load_system("mutual_ex")
        log(sys)

        subgoals = load_hints("mutual_ex_hints")

        failed = 0
        for inv_id, rule_id, case_id, hint in subgoals:
            goal, ans = sys.verify_subgoal(inv_id, rule_id, case_id, hint)
            log(printer.print_term(sys.thy, goal), " --- ", "OK" if ans else "FAIL")
            if not ans:
                failed += 1

        log("Number failed: " + str(failed))
        self.assertEqual(failed, 0)

        sys.add_invariant()
        sys.add_semantics()
        sys.get_proof()

    def testGerman(self):
        sys = load_system("german")
        log(sys)

        subgoals = load_hints("german_hints")

        failed = 0
        for inv_id, rule_id, case_id, hint in subgoals:
            goal, ans = sys.verify_subgoal(inv_id, rule_id, case_id, hint)
            log(printer.print_term(sys.thy, goal), " --- ", "OK" if ans else "FAIL")
            if not ans:
                failed += 1

        log("Number failed: " + str(failed))
        self.assertEqual(failed, 0)


if __name__ == "__main__":
    unittest.main()
