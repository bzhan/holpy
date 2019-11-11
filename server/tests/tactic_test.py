# Author: Bohua Zhan

import unittest

from kernel.type import boolT
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof, ProofItem, ItemID
from logic.proofterm import ProofTerm, ProofTermAtom
from logic import basic
from data.nat import natT, plus, zero
from server import tactic
from syntax import parser
from syntax import printer
from syntax.context import Context


class TacticTest(unittest.TestCase):
    def run_test(self, thy, tactic, *, vars=None, prevs=None, goal, args=None, new_goals=None, failed=None):
        """Test a single invocation of a tactic."""
        ctxt = Context(thy, vars=vars)
        thy = ctxt.thy

        assms = [parser.parse_term(ctxt, prev) for prev in prevs] if prevs is not None else []
        prf = Proof(*assms)
        prevs = [ProofTermAtom(i, Thm([], assm)) for i, assm in enumerate(assms)]
        goal = parser.parse_term(ctxt, goal)
        goal_pt = ProofTerm.sorry(Thm(assms, goal))

        # Invoke the tactic to get the proof term
        if failed is not None:
            self.assertRaises(failed, tactic.get_proof_term, thy, goal_pt, prevs=prevs, args=args)
            return

        pt = tactic.get_proof_term(thy, goal_pt, prevs=prevs, args=args)

        # Export and check proof
        prefix = ItemID(len(prevs)-1) if len(prevs) > 0 else ItemID(len(prevs))
        prf = pt.export(prefix=prefix, prf=prf, subproof=False)
        self.assertEqual(thy.check_proof(prf), Thm(assms, goal))

        # Test agreement of new goals
        new_goals = [parser.parse_term(ctxt, new_goal)
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
        n = Var("n", natT)
        self.run_test(
            'nat', tactic.rule(),
            vars={"n": "nat"},
            goal="n + 0 = n",
            args=("nat_induct", ({}, {'P': Term.mk_abs(n, Term.mk_equals(plus(n, zero), n)), 'x': n})),
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
        n = Var("n", natT)
        self.run_test(
            'nat', tactic.var_induct(),
            vars={"n": "nat"},
            goal="n + 0 = n",
            args=("nat_induct", n),
            new_goals=["(0::nat) + 0 = 0", "!n. n + 0 = n --> Suc n + 0 = Suc n"]
        )

    def testInduct2(self):
        thy = basic.load_theory('list')
        xs = Var("xs", parser.parse_type(thy, "'a list"))
        self.run_test(
            'list', tactic.var_induct(),
            vars={"xs": "'a list"},
            goal="xs @ [] = xs",
            args=("list_induct", xs),
            new_goals=["([]::'a list) @ [] = []", "!x::'a. !xs. xs @ [] = xs --> (x # xs) @ [] = x # xs"]
        )

    def testRewrite(self):
        self.run_test(
            'nat', tactic.rewrite(),
            vars={"n": "nat"},
            goal="0 + n = n",
            args="nat_plus_def_1"
        )

    def testRewrite2(self):
        self.run_test(
            'logic_base', tactic.rewrite(),
            vars={"a": "'a", "b": "'a"},
            goal="(if a = a then b else a) = b",
            args="if_P",
            new_goals=["a = a"]
        )

    def testRewrite3(self):
        self.run_test(
            'logic_base', tactic.rewrite(),
            vars={'P': 'bool', 'a': "'a", 'b': "'a"},
            prevs=["P"],
            goal="(if P then a else b) = a",
            args="if_P"
        )

    def testRewrite4(self):
        self.run_test(
            'logic_base', tactic.rewrite(),
            vars={'P': 'bool', 'Q': 'bool', 'a': "'a", 'b': "'a"},
            prevs=["Q"],
            goal="(if P then a else b) = a",
            args="if_P",
            failed=AssertionError
        )

    def testCases(self):
        A = Var('A', boolT)
        self.run_test(
            'logic_base', tactic.cases(),
            vars={'A': 'bool', 'B': 'bool', 'C': 'bool'},
            goal='C',
            args=A,
            new_goals=["A --> C", "~A --> C"]
        )


if __name__ == "__main__":
    unittest.main()
