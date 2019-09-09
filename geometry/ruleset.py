"""Set of rules."""

from geometry.expr import Fact, Rule
from geometry import parser

ruleset_raw = {
    "D1": "coll(A, C, B) :- coll(A, B, C)",
    "D2": "coll(B, A, C) :- coll(A, B, C)",
    "D3": "coll(C, D, A) :- coll(A, B, C), coll(A, B, D)",
    "D5": "para(m, l) :- para(l, m)",
    "D6": "para(l, n) :- para(l, m), para(m, n)",
    "D8": "perp(m, l) :- perp(l, m)",
    "D9": "para(l, n) :- perp(l, m), perp(m, n)",
    # "D42": "cyclic(A, B, P, Q) :- eqangle(P, A, P, B, Q, A, Q, B), coll(P, Q, A, B)",
    "D44": "para(E, F, B, C) :- midp(E, A, B), midp(F, A, C)",
    "D45": "midp(F, A, C) :- midp(E, A, B), para({E, F}, {B, C}), coll(F, A, C)",
    "D56": "perp({A, B}, {P, Q}) :- cong({A, P}, {B, P}), cong({A, Q}, {B, Q})",
}

ruleset = dict()
for name, s in ruleset_raw.items():
    ruleset[name] = parser.parse_rule(s)
