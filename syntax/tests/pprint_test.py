# Author: Bohua Zhan

import unittest

from logic import basic
from syntax import parser
from syntax import pprint


class PPrintTest(unittest.TestCase):
    def run_test(self, thy_name, s, expected_res, *, line_length=80):
        thy = basic.load_theory(thy_name)
        ctxt = {'vars': {}}
        t = parser.parse_term(thy, ctxt, s)
        ast = pprint.get_ast_term(thy, t, unicode=True)
        res = pprint.print_ast(thy, ast, line_length=line_length)
        self.assertEqual(res, expected_res)

    def testPPrint1(self):
        self.run_test(
            'realanalysis',
            "a ≤ b ∧ continuous_on (λx. f x * g x) (real_closed_interval a b) ∧ (∀x. x ∈ real_closed_interval a b ⟶ has_v_derivative f (f2 x) (at x) ∧ has_v_derivative g (g2 x) (at x)) ∧ has_integral (λx. f x * g2 x) (f b * g b - f a * g a - y) (real_closed_interval a b) ⟶ has_integral (λx. f2 x * g x) y (real_closed_interval a b)",
            [
                'a ≤ b ∧ ',
                'continuous_on (λx. f x * g x) (real_closed_interval a b) ∧ ',
                '(∀x. x ∈ real_closed_interval a b ',
                '   ⟶ has_v_derivative f (f2 x) (at x) ∧ has_v_derivative g (g2 x) (at x)) ∧ ',
                'has_integral (λx. f x * g2 x) (f b * g b - f a * g a - y) ',
                '  (real_closed_interval a b) ',
                '⟶ has_integral (λx. f2 x * g x) y (real_closed_interval a b)'
            ]
        )

    def testPPrint2(self):
        self.run_test(
            'logic_base',
            'long_constant_1 --> long_constant_2 --> long_constant1 & long_constant_2',
            [
                'long_constant_1 ',
                '⟶ long_constant_2 ',
                '   ⟶ long_constant1 ∧ long_constant_2'
            ],
            line_length=40
        )

    def testPPrint3(self):
        thy = basic.load_theory('realanalysis')
        ctxt = {'vars': {}}
        s = "real_bounded t ∧ t ⊆ s ⟶ real_bounded s"
        t = parser.parse_term(thy, ctxt, s)
        ast = pprint.get_ast_term(thy, t, unicode=True)
        res = pprint.print_ast(thy, ast, highlight=True, line_length=80)
        expected_res = [[
            {'text': 'real_bounded', 'color': 0, 'link_name': '', 'link_ty': 1},
            {'text': ' ', 'color': 0},
            {'text': 't', 'color': 2},
            {'text': ' ', 'color': 0},
            {'text': '∧', 'color': 0, 'link_name': 'conj', 'link_ty': 1},
            {'text': ' ', 'color': 0},
            {'text': 't', 'color': 2},
            {'text': ' ', 'color': 0},
            {'text': '⊆', 'color': 0, 'link_name': 'subset', 'link_ty': 1},
            {'text': ' ', 'color': 0},
            {'text': 's', 'color': 2},
            {'text': ' ', 'color': 0},
            {'text': '⟶', 'color': 0, 'link_name': 'implies', 'link_ty': 1},
            {'text': ' ', 'color': 0},
            {'text': 'real_bounded', 'color': 0, 'link_name': '', 'link_ty': 1},
            {'text': ' ', 'color': 0},
            {'text': 's', 'color': 2}
        ]]
        self.assertEqual(res, expected_res)


if __name__ == "__main__":
    unittest.main()
