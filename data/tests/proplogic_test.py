import unittest
from data import proplogic
from kernel.term import BoolVars, And, Or, Not
from logic import context
from logic.tests.conv_test import test_conv
from syntax import parser

A, B, C, D, E, F, G, P, Q, R = BoolVars('A B C D E F G P Q R')

class PropLogicTest(unittest.TestCase):
    def testNNFConv(self):
        test_data = [
            ("A", "A"),
            ("A & B", "A & B"),
            ("~A", "~A"),
            ("~~A", "A"),
            ("~~~A", "~A"),
            ("~~~~A", "A"),
            ("~(A & B)", "~A | ~B"),
            ("~(A | B)", "~A & ~B"),
            ("~(~A & ~B)", "A | B"),
            ("~(~A | ~B)", "A & B"),
            ("~(A & B & C)", "~A | ~B | ~C"),
            ("~((A & B) & C)", "(~A | ~B) | ~C"),
            ("~((~A | B) & ~C)", "(A & ~B) | C")
        ]

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.nnf_conv(), vars=vars, t=t, t_res=res)

    def testSwapConjRConv(self):
        test_data = [
            ('A & B', 'B & A'),
            ('A & B & C', 'B & A & C'),
        ]

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.swap_conj_r(), vars=vars, t=t, t_res=res)  

    def testNormConjAtomConv(self):
        test_data = [
            ('B & A & C', 'A & B & C'),
            ('true & A', 'A'),
            ('A & true', 'A'),
            ('true & A & C', 'A & C'),
            ('false & A & C', 'false'),
            ('A & false', 'false'),
            ('C & A & B', 'A & B & C'),
            ('B & ~B & A', 'false'),
            ('~B & B & A', 'false'),
            ('~C & A & C', 'false')
        ]      

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.norm_conj_atom(), vars=vars, t=t, t_res=res)

    def testNormConjConjunction(self):
        test_data = [
            ('(A & B) & (C & D)', 'A & B & C & D'),
            ('(C & D) & (A & B)', 'A & B & C & D')
        ]  

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.norm_conj_conjunction(), vars=vars, t=t, t_res=res)

    def testSwapDisjRConv(self):
        test_data = [
            ('A | B', 'B | A'),
            ('A | B | C', 'B | A | C'),
        ]

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.swap_disj_r(), vars=vars, t=t, t_res=res)  

    def testNormDisjAtomConv(self):
        test_data = [
            ('B | A | C', 'A | B | C'),
            ('false | A', 'A'),
            ('A | false', 'A'),
            ('false | A | C', 'A | C'),
            ('true | A | C', 'true'),
            ('A | true', 'true'),
            ('C | A | B', 'A | B | C'),
            ('B | ~B | A', 'true'),
            ('~B | B | A', 'true'),
            ('A & C | A & B', 'A & B | A & C'),
            ('D & E | A & C', 'A & C | D & E'),
        ]      

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.norm_disj_atom(), vars=vars, t=t, t_res=res)

    def testNormDisjDisjunction(self):
        test_data = [
            ('(A | B) | (C | D)', 'A | B | C | D'),
            ('(C | D) | (A | B)', 'A | B | C | D')
        ]  

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.norm_disj_disjunction(), vars=vars, t=t, t_res=res)

    def testSortConjuntion(self):
        test_data = [
            ('A & ~A', 'false'),
            ('A & B & ~A', 'false'),
            ('A & C & B', 'A & B & C'),
            ('A & (A & C) & B', 'A & B & C'),
            ('~A & C & (B & false)', 'false'),
            ('A & true', 'A'),
            ('false & A', 'false')
        ]
        vars = {"A": "bool", "B" : "bool", "C": "bool", "D": "bool",
                "E": "bool", "F" : "bool", "G": "bool", "H": "bool"}
        context.set_context('logic', vars=vars)

        for t, t_res in test_data:
            t, t_res = parser.parse_term(t), parser.parse_term(t_res)
            test_conv(self, 'logic', proplogic.sort_conj(), vars=vars, t=t, t_res=t_res)

    def testSortDisjunction(self):
        test_data = [
            ('A | ~A', 'true'),
            ('A | B | ~A', 'true'),
            ('A | B | (true | false) | C', 'true'),
            ('A | false', 'A'),
            ('B | (A | C) | (E | A) | D', 'A | B | C | D | E')
        ]

        vars = {"A": "bool", "B" : "bool", "C": "bool", "D": "bool",
                "E": "bool", "F" : "bool", "G": "bool", "H": "bool"}
        context.set_context('logic', vars=vars)

        for t, t_res in test_data:
            t, t_res = parser.parse_term(t), parser.parse_term(t_res)
            test_conv(self, 'logic', proplogic.sort_disj(), vars=vars, t=t, t_res=t_res)