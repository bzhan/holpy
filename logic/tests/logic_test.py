# Author: Bohua Zhan

import unittest

from kernel.type import TVar, TFun, boolT
from kernel import term
from kernel.term import Term, Var, Abs, Bound, And, Or, Eq
from kernel.macro import global_macros
from kernel.thm import Thm
from kernel.proof import Proof
from kernel.report import ProofReport
from kernel import theory
from logic.proofterm import ProofTerm, ProofTermDeriv
from logic import logic
from logic import basic
from logic import matcher
from logic.tests.conv_test import test_conv
from data import nat
from syntax import parser
from logic import context

Ta = TVar("a")
a = Var("a", boolT)
b = Var("b", boolT)
c = Var("c", boolT)
d = Var("d", boolT)
x = Var("x", Ta)
y = Var("y", Ta)

def test_macro(self, thy_name, macro, *, vars=None, assms=None, res=None, args="", failed=None,
               limit=None, eval_only=False):
    context.set_context(thy_name, vars=vars, limit=limit)

    macro = global_macros[macro]
    assms = [parser.parse_term(assm) for assm in assms] if assms is not None else []
    prev_ths = [Thm([assm], assm) for assm in assms]
    prevs = [ProofTerm.assume(assm) for assm in assms]
    args = parser.parse_args(macro.sig, args)

    if failed is not None:
        self.assertRaises(failed, macro.eval, args, prev_ths)
        if not eval_only:
            self.assertRaises(failed, macro.get_proof_term, args, prevs)
        return

    res = parser.parse_term(res)

    # Check the eval function
    self.assertEqual(macro.eval(args, prev_ths), Thm(assms, res))

    # Check the proof term
    if not eval_only:
        pt = macro.get_proof_term(args, prevs)
        prf = pt.export()
        self.assertEqual(theory.thy.check_proof(prf), Thm(assms, res))

class LogicTest(unittest.TestCase):
    def testGetForallName(self):
        test_data = [
            (Term.mk_all(x, Term.mk_all(y, Eq(x, y))), ["x", "y"]),
        ]

        for t, res in test_data:
            self.assertEqual(logic.get_forall_names(t), res)

    def testNormBoolExpr(self):
        test_data = [
            ("true", "true"),
            ("false", "false"),
            ("~true", "false"),
            ("~false", "true"),
        ]

        for t, t_res in test_data:
            test_conv(self, 'logic', logic.norm_bool_expr(), t=t, t_res=t_res)

    def testNormConjAssoc(self):
        test_data = [
            ("A", "A"),
            ("A & B", "A & B"),
            ("(A & B) & (C & D)", "A & B & C & D"),
            ("((A & B) & C) & D", "A & B & C & D"),
        ]

        vars = {'A': 'bool', 'B': 'bool'}
        for t, t_res in test_data:
            test_conv(self, 'logic', logic.norm_conj_assoc(), vars=vars, t=t, t_res=t_res)

    def testBetaNorm(self):
        test_macro(
            self, 'logic_base', "beta_norm",
            vars={'f': "'a => 'b", 'x': "'a", 'y': "'b"},
            assms=["(%x. f x) x = y"],
            res="f x = y")

    def testApplyTheorem(self):
        test_macro(
            self, 'logic_base', "apply_theorem",
            vars={'A': 'bool', 'B': 'bool'},
            assms=["A & B"],
            args="conjD1",
            res="A"
        )

    def testApplyTheorem2(self):
        test_macro(
            self, 'set', 'apply_theorem',
            vars={'A': "'a set", 'B': "'a set", 'C': "'a set"},
            assms=["A Sub B"],
            args="subset_trans",
            res="!C. B Sub C --> A Sub C"
        )

    def testApplyTheorem3(self):
        test_macro(
            self, 'set', 'apply_theorem_for',
            vars={'A': 'nat set'},
            args="subset_trans, {a: nat}, {A: A}",
            res="!B. !C. A Sub B --> B Sub C --> A Sub C"
        )

    def testIntro(self):
        basic.load_theory('logic_base')
        macro = logic.intros_macro()

        Ta = TVar('a')
        x = Var('x', Ta)
        P = Var('P', TFun(Ta, boolT))
        C = Var('C', boolT)
        ex_P = logic.mk_exists(x, P(x))
        pt1 = ProofTerm.assume(ex_P)
        pt2 = ProofTerm.variable('x', Ta)
        pt3 = ProofTerm.assume(P(x))
        pt4 = ProofTerm.sorry(Thm([P(x)], C))
        pt4 = ProofTermDeriv('intros', args=[ex_P], prevs=[pt1, pt2, pt3, pt4])
        prf = pt4.export()
        self.assertEqual(theory.thy.check_proof(prf), Thm([ex_P], C))

    def testRewriteGoal(self):
        test_macro(
            self, 'nat', "rewrite_goal",
            args=("nat_plus_def_1, (0::nat) + 0 = 0"),
            res="(0::nat) + 0 = 0"
        )

    def testRewriteGoal2(self):
        test_macro(
            self, 'set', 'rewrite_goal_sym',
            vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set"},
            args=("image_combine, image f (image g s) = t"),
            assms=["image (f O g) s = t"],
            res="image f (image g s) = t"
        )

    def testRewriteFactWithPrev(self):
        test_macro(
            self, 'nat', 'rewrite_fact_with_prev',
            vars={'m': 'nat', 'n': 'nat', 'p': 'nat', 'q': 'nat'},
            assms=['p = m + n', 'p = q'],
            res='m + n = q'
        )

    def testRewriteFactWithPrev2(self):
        test_macro(
            self, 'nat', 'rewrite_fact_with_prev',
            vars={'f': 'nat => nat', 'g': 'nat => nat', 'a': 'nat'},
            assms=['!n. f n = g n', 'f x = a'],
            res='g x = a'
        )

    def testRewriteFactWithPrev3(self):
        test_macro(
            self, 'nat', 'rewrite_fact_with_prev',
            vars={'f': 'nat => nat', 'g': 'nat => nat', 'a': 'nat'},
            assms=['!n. f n = g n', '?x. f x = a'],
            res='?x. g x = a'
        )

    def testForallElimGen(self):
        test_macro(
            self, 'nat', 'forall_elim_gen',
            vars={'n': 'nat'},
            assms=['!P::nat => bool. P n'],
            args="%n::nat. n > 2",
            res="n > 2"
        )

    def testTrivialMacro(self):
        test_macro(
            self, 'logic_base', 'trivial',
            vars={'A': 'bool', 'B': 'bool'},
            args='A --> B --> A',
            res='A --> B --> A'
        )

    def testTrivialMacro2(self):
        test_macro(
            self, 'logic_base', 'trivial',
            vars={'A': 'bool', 'B': 'bool'},
            args='A --> A --> B --> A',
            res='A --> A --> B --> A'
        )

    def testTrivialMacro3(self):
        test_macro(
            self, 'logic_base', 'trivial',
            vars={'P': "'a => bool", 'Q': "'a => bool"},
            args='!x. P x --> Q x --> P x',
            res='!x. P x --> Q x --> P x'
        )

    def testApplyFactMacro(self):
        test_macro(
            self, 'logic_base', 'apply_fact',
            vars={"P": "'a => bool", "Q": "'a => bool", "s": "'a"},
            assms=["!s. P s --> Q s", "P s"],
            res="Q s"
        )

    def testApplyFactMacro2(self):
        test_macro(
            self, 'logic_base', 'apply_fact',
            vars={'P': "'a => bool", 'R': "'a => 'a => bool", 's': "'a"},
            assms=['!x. !y. P x --> R x y', 'P s'],
            res="!y. R s y"
        )

    def testApplyFactMacro3(self):
        test_macro(
            self, 'logic_base', 'apply_fact',
            vars={'P': "'a => bool", 'R': "'a => 'a => bool", 's': "'a"},
            assms=['!x. !y. P y --> R x y', 'P s'],
            res="!x. R x s"
        )

    def testImpConjMacro(self):
        test_data = [
            ('A & (D & B) & C --> (A & D & C) & (A & B)', True),
            ('C & D --> A', False),
            ('A & B --> A & B & C', False),
            ('A & B & C --> A & B', True)
        ]

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool', 'D': 'bool'}
        for t, success in test_data:
            if success:
                test_macro(self, 'logic_base', 'imp_conj', vars=vars, args=t, res=t)
            else:
                test_macro(self, 'logic_base', 'imp_conj', vars=vars, args=t, failed=AssertionError)


if __name__ == "__main__":
    unittest.main()
