import unittest
from kernel.type import TConst, TFun, BoolType, RealType, IntType
from kernel.term import *
from smt.veriT.parser import parse_type, parse_step

x_1 = Var("x_1", IntType)
x_2 = Var("x_2", IntType)
x_3 = Var("x_3", IntType)

y_1 = Var("y_1", RealType)
y_2 = Var("y_2", RealType)
y_3 = Var("y_3", RealType)

P = Var("P", BoolType)
Q = Var("Q", BoolType)
R = Var("R", BoolType)

S = Var("S", TFun(IntType, BoolType))
T = Var("T", TFun(IntType, BoolType))

class VeriTParserTest(unittest.TestCase):

    def testParseType(self):
        test_data = [
            ("(declare-sort utt$16 0)", TConst("utt$16")),
            ("(declare-fun x0 () Int)", Var("x0", IntType)),
            ("(declare-fun prt () Bool)", Var("prt", BoolType)),
            ("(declare-fun Concat_16_10_6 (utt$10 utt$6 ) utt$16)", 
            Var("Concat_16_10_6", TFun(TConst("utt$10"), TConst("utt$6"), TConst("utt$16"))))
        ]

        for v, v_res in test_data:
            v = parse_type(v)
            self.assertEqual(v, v_res)

    def testParser(self):
        test_data = [
            ("x_1", x_1),
            ("(+ x_1 x_2)", x_1 + x_2),
            ("(- x_1 (+ x_2 x_1))", x_1 - (x_2 + x_1)),
            ("(not P)", Not(P)),
            ("(and P Q)", And(P, Q)),
            ("(or P Q R)", Or(P, Q, R)),
            ("(and (or P Q) R)", And(Or(P, Q), R)),
            ("(=> P (> x_1 x_2))", Implies(P, x_1 > x_2)),
            ("(T x_1)", T(x_1)),
            ("#10:(forall ( (x_1 Int) ) #11:(=> #12:(S x_1) #13:(T x_1)))", 
            Forall(x_1, Implies(S(x_1), T(x_1)))),
        ]

        sorts = {"x_1": x_1, "x_2": x_2, "P": P, "Q": Q, "R": R, "T": T, "S": S}

        for v, v_res in test_data:
            self.assertEqual(parse_step(v, sorts), v_res)

    

if __name__ == "__main__":
    unittest.main()
