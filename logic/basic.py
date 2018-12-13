# Author: Bohua Zhan

import io
import json
import os

from kernel.type import TVar, TFun, Type, hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.theory import Theory
from logic.operator import OperatorTable
from logic.nat import Nat
from logic import logic, logic_macro, induct
from syntax import parser


def getBasicTheory():
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", OperatorTable())
    script_dir = os.path.dirname(__file__)
    with io.open(os.path.join(script_dir, 'basic.json'), encoding="utf-8") as a:
        data = json.load(a)

    parser.parse_extensions(thy, data)

    # Natural numbers
    nat = Type("nat")
    nat_ext = induct.add_induct_type(
        "nat", [], [("zero", nat, []), ("Suc", TFun(nat, nat), ["n"])])
    thy.unchecked_extend(nat_ext)

    m = Var("m", nat)
    n = Var("n", nat)
    P = Var("P", TFun(nat, hol_bool))
    eq = Term.mk_equals
    S = Nat.Suc
    plus = Nat.plus
    times = Nat.times

    # Addition on natural numbers
    thy.unchecked_extend(induct.add_induct_def(plus, [
        Thm([], eq(plus(Nat.zero, n), n)),
        Thm([], eq(plus(S(m), n), S(plus(m, n))))]))

    # Multiplication on natural numbers
    thy.unchecked_extend(induct.add_induct_def(times, [
        Thm([], eq(times(Nat.zero, n), Nat.zero)),
        Thm([], eq(times(S(m), n), plus(n, times(m, n))))]))

    # Basic macros
    thy.add_proof_macro("arg_combination", logic_macro.arg_combination_macro())
    thy.add_proof_macro("fun_combination", logic_macro.fun_combination_macro())
    thy.add_proof_macro("beta_norm", logic_macro.beta_norm_macro())
    thy.add_proof_macro("apply_theorem", logic_macro.apply_theorem_macro())
    thy.add_proof_macro("apply_theorem_for", logic_macro.apply_theorem_macro(with_inst=True))
    thy.add_proof_macro("rewrite_goal", logic_macro.rewrite_goal_macro())
    thy.add_proof_macro("rewrite_back_goal", logic_macro.rewrite_goal_macro(backward=True))
    return thy

BasicTheory = getBasicTheory()
