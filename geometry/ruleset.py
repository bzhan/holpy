"""Set of rules."""

from geometry.expr import Fact, Rule
from geometry import parser

ruleset_raw = {
    "D1": "coll(A, C, B) :- coll(A, B, C)",
    "D2": "coll(B, A, C) :- coll(A, B, C)",
    "D3": "coll(C, D, A) :- coll(A, B, C), coll(A, B, D)",
    "D5": "para({C, D}, {A, B}) :- para({A, B}, {C, D})",
    "D6": "para(l, n) :- para(l, m), para(m, n)",
    "D7": "perp({A, B}, {D, C}) :- perp({A, B}, {C, D})",
    "D8": "perp({C, D}, {A, B}) :- perp({A, B}, {C, D})",
    "D9": "para({A, B}, {E, F}) :- perp({A, B}, {C, D}), perp({C, D}, {E, F})",
    # "D42": "cyclic(A, B, P, Q) :- eqangle(P, A, P, B, Q, A, Q, B), coll(P, Q, A, B)",
    "D44": "para(E, F, B, C) :- midp(E, A, B), midp(F, A, C)",
    "D45": "midp(F, A, C) :- midp(E, A, B), para({E, F}, {B, C}), coll(F, A, C)",
    "D56": "perp({A, B}, {P, Q}) :- cong({A, P}, {B, P}), cong({A, Q}, {B, Q})",
}

ruleset = dict()
for name, s in ruleset_raw.items():
    ruleset[name] = parser.parse_rule(s)
