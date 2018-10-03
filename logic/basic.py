# Author: Bohua Zhan

import abc
from kernel.thm import *
from kernel.proof import *
from kernel.theory import *
from kernel.macro import ProofMacro

def arg_combination_eval(th, f):
    assert th.concl.is_equals(), "arg_combination"
    return Thm.combination(Thm.reflexive(f), th)

def arg_combination_expand(depth, ids, th, f):
    assert th.concl.is_equals(), "arg_combination"

    th1 = Thm.reflexive(f)
    th2 = Thm.combination(th1, th)
    prf = Proof()
    prf.add_item((depth, "S1"), th1, "reflexive", args = f)
    prf.add_item("C", th2, "combination", prevs = [(depth, "S1"), ids[0]])
    return prf

arg_combination_macro = ProofMacro(
    "Given theorem x = y and term f, return f x = f y.",
    arg_combination_eval,
    arg_combination_expand,
    level = 1
)

def fun_combination_eval(th, f):
    assert th.concl.is_equals(), "fun_combination"
    return Thm.combination(th, Thm.reflexive(f))

def fun_combination_expand(depth, ids, th, f):
    assert th.concl.is_equals(), "fun_combination"

    th1 = Thm.reflexive(f)
    th2 = Thm.combination(th, th1)
    prf = Proof()
    prf.add_item((depth, "S1"), th1, "reflexive", args = f)
    prf.add_item("C", th2, "combination", prevs = [ids[0], (depth, "S1")])
    return prf

fun_combination_macro = ProofMacro(
    "Given theorem f = g and term x, return f x = g x.",
    fun_combination_eval,
    fun_combination_expand,
    level = 1
)

def BasicTheory():
    thy = Theory.EmptyTheory()
    thy.add_proof_macro("arg_combination", arg_combination_macro)
    thy.add_proof_macro("fun_combination", fun_combination_macro)
    return thy

