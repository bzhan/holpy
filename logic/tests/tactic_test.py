# Author: Bohua Zhan

import unittest

from kernel.type import BoolType, NatType
from kernel.term import Term, Var, Eq, Lambda, Inst
from kernel.thm import Thm
from kernel.proof import Proof, ProofItem, ItemID
from kernel import theory
from kernel.proofterm import ProofTerm
from logic import basic
from logic import tactic
from logic import context
from syntax import parser


class TacticTest(unittest.TestCase):
    def run_test(self, thy_name, tactic, *, vars=None, prevs=None, goal, args=None, new_goals=None, failed=None):
        """Test a single invocation of a tactic."""
        context.set_context(thy_name, vars=vars)

        if prevs is not None:
            assms = tuple(parser.parse_term(prev) for prev in prevs)
        else:
            assms = tuple()
        prf = Proof(*assms)
        prevs = [ProofTerm.atom(i, Thm.assume(assm)) for i, assm in enumerate(assms)]
        goal = parser.parse_term(goal)
        goal_pt = ProofTerm.sorry(Thm(goal, assms))

        # Invoke the tactic to get the proof term
        if failed is not None:
            self.assertRaises(failed, tactic.get_proof_term, goal_pt, prevs=prevs, args=args)
            return

        pt = tactic.get_proof_term(goal_pt, prevs=prevs, args=args)

        # Export and check proof
        prefix = ItemID(len(prevs)-1) if len(prevs) > 0 else ItemID(len(prevs))
        prf = pt.export(prefix=prefix, prf=prf, subproof=False)
        self.assertEqual(theory.check_proof(prf), Thm(goal, assms))

        # Test agreement of new goals
        new_goals = [parser.parse_term(new_goal)
                     for new_goal in new_goals] if new_goals is not None else []
        concls = [goal.prop for goal in prf.get_sorrys()]
        self.assertEqual(new_goals, concls)

    def testRule(self):
        self.run_test(
            'logic_base', tactic.rule(),
            vars={"A": "bool", "B": "bool"},
            goal="B & A",
            args="conjI",
            new_goals=["B", "A"]
        )

    def testRule2(self):
        self.run_test(
            'logic_base', tactic.rule(),
            vars={"A": "bool", "B": "bool"},
            prevs=["A | B"],
            goal="B | A",
            args="disjE",
            new_goals=["A --> B | A", "B --> B | A"]
        )

    def testRule3(self):
        self.run_test(
            'logic_base', tactic.rule(),
            vars={"A": "bool", "B": "bool"},
            prevs=["B"],
            goal="B | A",
            args="disjI1"
        )

    def testRule4(self):
        n = Var("n", NatType)
        self.run_test(
            'nat', tactic.rule(),
            vars={"n": "nat"},
            goal="n + 0 = n",
            args=("nat_induct", Inst(P=Lambda(n, Eq(n + 0, n)), x=n)),
            new_goals=["(0::nat) + 0 = 0", "!n. n + 0 = n --> Suc n + 0 = Suc n"]
        )

    def testRule5(self):
        self.run_test(
            'set', tactic.rule(),
            goal="finite (empty_set::nat set)",
            args="finite_empty"
        )

    def testIntros(self):
        self.run_test(
            'logic_base', tactic.intros(),
            vars={"x": "'a", "P": "'a => bool", "Q": "'a => bool"},
            goal="!x. P x --> Q x",
            args=["x"],
            new_goals=["Q x"]
        )

    def testIntros2(self):
        self.run_test(
            'logic_base', tactic.intros(),
            vars={"x": "'a", "y": "'b", "R": "'a => 'b => bool"},
            goal="!x. !y. R x y",
            args=["x", "y"],
            new_goals=["R x y"]
        )

    def testInduct(self):
        n = Var("n", NatType)
        self.run_test(
            'nat', tactic.var_induct(),
            vars={"n": "nat"},
            goal="n + 0 = n",
            args=("nat_induct", n),
            new_goals=["(0::nat) + 0 = 0", "!n. n + 0 = n --> Suc n + 0 = Suc n"]
        )

    def testInduct2(self):
        basic.load_theory('list')
        xs = Var("xs", parser.parse_type("'a list"))
        self.run_test(
            'list', tactic.var_induct(),
            vars={"xs": "'a list"},
            goal="xs @ [] = xs",
            args=("list_induct", xs),
            new_goals=["([]::'a list) @ [] = []", "!x::'a. !xs. xs @ [] = xs --> (x # xs) @ [] = x # xs"]
        )

    def testRewrite(self):
        self.run_test(
            'nat', tactic.rewrite_goal(),
            vars={"n": "nat"},
            goal="0 + n = n",
            args="nat_plus_def_1"
        )

    def testRewrite2(self):
        self.run_test(
            'logic_base', tactic.rewrite_goal(),
            vars={"a": "'a", "b": "'a"},
            goal="(if a = a then b else a) = b",
            args="if_P",
            failed=AssertionError
        )

    def testRewrite3(self):
        self.run_test(
            'logic_base', tactic.rewrite_goal(),
            vars={'P': 'bool', 'a': "'a", 'b': "'a"},
            prevs=["P"],
            goal="(if P then a else b) = a",
            args="if_P"
        )

    def testRewrite4(self):
        self.run_test(
            'logic_base', tactic.rewrite_goal(),
            vars={'P': 'bool', 'Q': 'bool', 'a': "'a", 'b': "'a"},
            prevs=["Q"],
            goal="(if P then a else b) = a",
            args="if_P",
            failed=AssertionError
        )

    def testRewriteGoalWithPrev(self):
        self.run_test(
            'nat', tactic.rewrite_goal_with_prev(),
            vars={'m': 'nat', 'n': 'nat', 'q': 'nat'},
            prevs=['p = m + n'],
            goal='p = q',
            new_goals=['m + n = q']
        )

    def testRewriteGoalWithPrev2(self):
        self.run_test(
            'nat', tactic.rewrite_goal_with_prev(),
            vars={'a': 'nat', 'f': 'nat => nat', 'g': 'nat => nat'},
            prevs=['!n. f n = g n'],
            goal='f n = a',
            new_goals=['g n = a']
        )

    def testRewriteGoalWithPrev3(self):
        self.run_test(
            'nat', tactic.rewrite_goal_with_prev(),
            vars={'a': 'nat', 'f': 'nat => nat', 'g': 'nat => nat'},
            prevs=['!n. f n = g n'],
            goal='?x. f x = a',
            new_goals=['?x. g x = a']
        )

    def testCases(self):
        A = Var('A', BoolType)
        self.run_test(
            'logic_base', tactic.cases(),
            vars={'A': 'bool', 'B': 'bool', 'C': 'bool'},
            goal='C',
            args=A,
            new_goals=["A --> C", "~A --> C"]
        )


if __name__ == "__main__":
    unittest.main()
