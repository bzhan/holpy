# Author: Bohua Zhan

from kernel.type import TVar, TFun, Type, hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from kernel.theory import Theory
from logic.operator import OperatorTable
from logic.logic import Logic
from logic.nat import Nat
from logic.logic_macro import *
from logic import induct

def BasicTheory():
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", OperatorTable())

    # Logical terms
    thy.add_term_sig("conj", TFun(hol_bool, hol_bool, hol_bool))
    thy.add_term_sig("disj", TFun(hol_bool, hol_bool, hol_bool))
    thy.add_term_sig("neg", TFun(hol_bool, hol_bool))
    thy.add_term_sig("true", hol_bool)
    thy.add_term_sig("false", hol_bool)
    thy.add_term_sig("exists", TFun(TFun(TVar("a"), hol_bool), hol_bool))

    A = Var("A", hol_bool)
    B = Var("B", hol_bool)
    C = Var("C", hol_bool)
    imp = Term.mk_implies
    eq = Term.mk_equals

    # Axioms for conjugation
    conjAB = Logic.mk_conj(A, B)
    thy.add_theorem("conjI", Thm([], imp(A, B, conjAB)))
    thy.add_theorem("conjD1", Thm([], imp(conjAB, A)))
    thy.add_theorem("conjD2", Thm([], imp(conjAB, B)))

    # Axioms for disjunction
    disjAB = Logic.mk_disj(A, B)
    thy.add_theorem("disjI1", Thm([], imp(A, disjAB)))
    thy.add_theorem("disjI2", Thm([], imp(B, disjAB)))
    thy.add_theorem("disjE", Thm([], imp(disjAB, imp(A, C), imp(B, C), C)))

    # Axioms for negation
    thy.add_theorem("negI", Thm([], imp(imp(A, Logic.false), Logic.neg(A))))
    thy.add_theorem("negE", Thm([], imp(Logic.neg(A), A, Logic.false)))

    # Axioms for true
    thy.add_theorem("trueI", Thm([], Logic.true))

    # Axioms for false
    thy.add_theorem("falseE", Thm([], imp(Logic.false, A)))

    # Axioms for exists
    P = Var("P", TFun(TVar("a"), hol_bool))
    a = Var("a", TVar("a"))
    thy.add_theorem("exI", Thm([], imp(P(a), Logic.mk_exists(a, P(a)))))
    thy.add_theorem("exE", Thm([], imp(Logic.mk_exists(a, P(a)), Term.mk_all(a, imp(P(a), C)), C)))

    # Classical axiom
    thy.add_theorem("classical", Thm([], Logic.disj(A, Logic.neg(A))))

    # Natural numbers
    nat = Type("nat")
    nat_ext = induct.add_induct_type(
        "nat", [], [("0", nat, []), ("Suc", TFun(nat, nat), ["n"])])
    thy.unchecked_extend(nat_ext)

    m = Var("m", nat)
    n = Var("n", nat)
    P = Var("P", TFun(nat, hol_bool))
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
    thy.add_proof_macro("arg_combination", arg_combination_macro())
    thy.add_proof_macro("fun_combination", fun_combination_macro())
    thy.add_proof_macro("beta_norm", beta_norm_macro())
    thy.add_proof_macro("apply_theorem", apply_theorem_macro())
    thy.add_proof_macro("apply_theorem_for", apply_theorem_macro(with_concl=True))
    return thy
