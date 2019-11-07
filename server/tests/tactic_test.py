# Author: Bohua Zhan

import unittest

from kernel.type import boolT
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.proof import Proof, ProofItem
from logic.proofterm import ProofTerm, ProofTermAtom
from logic import basic
from data.nat import natT, plus, zero
from server import tactic
from syntax import parser
from syntax import printer


class TacticTest(unittest.TestCase):
    def run_test(self, thy_name, tactic, *, ctxt=None, prevs=None, goal, args=None, new_goals=None):
        """Test a single invocation of a tactic."""
        thy = basic.load_theory(thy_name)
        ctxt = {'vars': dict((nm, parser.parse_type(thy, s))
                             for nm, s in ctxt.items()) if ctxt is not None else {}}
        assms = [parser.parse_term(thy, ctxt, prev) for prev in prevs] if prevs is not None else []
        prf = Proof(*assms)
        prevs = [ProofTermAtom(i, Thm([], assm)) for i, assm in enumerate(assms)]
        goal = parser.parse_term(thy, ctxt, goal)

        # Invoke the tactic to get the proof term
        pt = tactic.get_proof_term(thy, ProofTerm.sorry(Thm([], goal)), prevs=prevs, args=args)

        # Export and check proof
        prefix = (len(prevs)-1,) if len(prevs) > 0 else (len(prevs),)
        prf = pt.export(prefix=prefix, prf=prf, subproof=False)
        self.assertEqual(thy.check_proof(prf), Thm(assms, goal))

        # Test agreement of new goals
        new_goals = [parser.parse_term(thy, ctxt, new_goal)
                     for new_goal in new_goals] if new_goals is not None else []
        concls = [goal.prop for goal in prf.get_sorrys()]
        self.assertEqual(new_goals, concls)

    def testRule(self):
        self.run_test(
            'logic_base', tactic.rule(),
            ctxt={"A": "bool", "B": "bool"},
            goal="B & A",
            args="conjI",
            new_goals=["B", "A"]
        )

    def testRule2(self):
        self.run_test(
            'logic_base', tactic.rule(),
            ctxt={"A": "bool", "B": "bool"},
            prevs=["A | B"],
            goal="B | A",
            args="disjE",
            new_goals=["A --> B | A", "B --> B | A"]
        )

    def testRule3(self):
        self.run_test(
            'logic_base', tactic.rule(),
            ctxt={"A": "bool", "B": "bool"},
            prevs=["B"],
            goal="B | A",
            args="disjI1"
        )

    def testRule4(self):
        n = Var("n", natT)
        self.run_test(
            'nat', tactic.rule(),
            ctxt={"n": "nat"},
            goal="n + 0 = n",
            args=("nat_induct", ({}, {'P': Term.mk_abs(n, Term.mk_equals(plus(n, zero), n)), 'x': n})),
            new_goals=["(0::nat) + 0 = 0", "!n. n + 0 = n --> Suc n + 0 = Suc n"]
        )

    def testIntros(self):
        self.run_test(
            'logic_base', tactic.intros(),
            ctxt={"x": "'a", "P": "'a => bool", "Q": "'a => bool"},
            goal="!x. P x --> Q x",
            args=["x"],
            new_goals=["Q x"]
        )

    def testInduct(self):
        n = Var("n", natT)
        self.run_test(
            'nat', tactic.var_induct(),
            ctxt={"n": "nat"},
            goal="n + 0 = n",
            args=("nat_induct", n),
            new_goals=["(0::nat) + 0 = 0", "!n. n + 0 = n --> Suc n + 0 = Suc n"]
        )

    def testRewrite(self):
        self.run_test(
            'nat', tactic.rewrite(),
            ctxt={"n": "nat"},
            goal="0 + n = n",
            args="nat_plus_def_1"
        )

    def testRewrite2(self):
        self.run_test(
            'logic_base', tactic.rewrite(),
            ctxt={"a": "'a", "b": "'a"},
            goal="(if a = a then b else a) = b",
            args="if_P",
            new_goals=["a = a"]
        )

    def testCases(self):
        A = Var('A', boolT)
        self.run_test(
            'logic_base', tactic.cases(),
            ctxt={'A': 'bool', 'B': 'bool', 'C': 'bool'},
            goal='C',
            args=A,
            new_goals=["A --> C", "~A --> C"]
        )


if __name__ == "__main__":
    unittest.main()
