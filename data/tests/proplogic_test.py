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
            ('~B & B & A', 'false')
        ]      

        vars = {'A': 'bool', 'B': 'bool', 'C': 'bool'}
        context.set_context('logic', vars=vars)
        for t, res in test_data:
            t, res = parser.parse_term(t), parser.parse_term(res)
            test_conv(self, 'logic', proplogic.norm_conj_atom(), vars=vars, t=t, t_res=res)        