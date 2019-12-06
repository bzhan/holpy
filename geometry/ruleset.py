"""Set of rules."""

from geometry.expr import Fact, Rule
from geometry import parser

ruleset_raw = {
    # "D1": "coll(A, C, B) :- coll(A, B, C)",
    # "D2": "coll(B, A, C) :- coll(A, B, C)",
    # "D3": "coll(C, D, A) :- coll(A, B, C), coll(A, B, D)",
    "D5": "para(m, l) :- para(l, m)",
    "D6": "para(l, n) :- para(l, m), para(m, n)",
    "D8": "perp(m, l) :- perp(l, m)",
    "D9": "para(l, n) :- perp(l, m), perp(m, n)",
    "D13": "cyclic(A, B, C, D) :- cong(O, A, O, B), cong(O, A, O, C), cong(O, A, O, D)",
    # "D17": "cyclic(B, C, D, E) :- cyclic(A, B, C, D), cyclic(A, B, C, E)",
    # Currently no need
    # "D18": "eqangle(B, A, l, m ,n) :- eqangle(A, B, l, m, n)",
    # "D19": "eqangle(l, k, n, m) :- eqangle(k, l, m, n)",
    # "D20": "eqangle(m ,n ,k ,l) :- eqangle(k, l ,m ,n)",
    "D21": "eqangle(k, m ,l, n) :- eqangle(k, l, m, n)",
    "D22": "eqangle(a, b, e, f) :- eqangle(a, b, c, d), eqangle(c, d, e, f)",
    # "D24": "cong(C, D, A, B) :- cong(A, B, C, D)",
    # "D25": "cong(A, B, E, F) :- cong(A, B, C, D), cong(C, D, E, F)",
    "D41": "eqangle(P, A, P, B, Q, A, Q, B) :- cyclic(A, B, P, Q)",
    # TODO: Support symbol "¬". Argument "¬coll(P,Q,A,B)" in D42 has been ignored.
    "D42": "cyclic(A, B, P, Q) :- eqangle(P, A, P, B, Q, A, Q, B)",
    # Match facts that are not "cyclic" or "circle" first. The order of arguments in D43 differ from the
    # original version.
    "D43": "cong(A, B, P, Q) :- eqangle(C, A, C, B, R, P, R, Q), cyclic(A, B, C, P, Q, R)",
    "D44": "para(E, F, B, C) :- midp(E, A, B), midp(F, A, C)",
    "D45": "midp(F, A, C) :- midp(E, A, B), para(E, F, B, C), coll(F, A, C)",
    "D46": "eqangle(O, A, A, B, A, B, O, B) :- cong(O, A, O, B)",
    "D56": "perp(A, B, P, Q) :- cong(A, P, B, P), cong(A, Q, B, Q)",
    # Use this rule to generate eqangle from two perp facts. (Written by myself)
    "D76": "eqangle(k, l, m, n) :- perp(k, l), perp(m ,n)",
    # (This one is also written by myself)
    "D77": "perp(m, n) :-  eqangle(k, l, m, n), perp(k, l)",
    "D78": "eqangle(l, k, m, n) :- perp(k, l), perp(m, n)",
}

ruleset = dict()
for name, s in ruleset_raw.items():
    ruleset[name] = parser.parse_rule(s)
