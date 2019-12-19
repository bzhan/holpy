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
    "D40": "eqangle(a, c, b, c) :- para(a, b)",
    "D41": "eqangle(P, A, P, B, Q, A, Q, B) :- cyclic(A, B, P, Q)",
    # TODO: Support symbol "¬". Argument "¬coll(P,Q,A,B)" in D42, D58 has been ignored.
    "D42": "cyclic(A, B, P, Q) :- eqangle(P, A, P, B, Q, A, Q, B)",
    # Match facts that are not "cyclic" or "circle" first. The order of arguments in D43 differ from the
    # original version.
    "D43": "cong(A, B, P, Q) :- eqangle(C, A, C, B, R, P, R, Q), cyclic(A, B, C, P, Q, R)",
    "D44": "para(E, F, B, C) :- midp(E, A, B), midp(F, A, C)",
    "D45": "midp(F, A, C) :- midp(E, A, B), para(E, F, B, C), coll(F, A, C)",
    "D46": "eqangle(O, A, A, B, A, B, O, B) :- cong(O, A, O, B)",
    "D56": "perp(A, B, P, Q) :- cong(A, P, B, P), cong(A, Q, B, Q)",
    "D58": "simtri(A, B, C, P, Q, R) :- eqangle(A, B, B, C, P, Q, Q, R), eqangle(A, C, B, C, P, R, Q, R)",
    "D61": "contri(A, B, C, P, Q, R) :- simtri(A, B, C, P, Q, R), cong(A, B, P, Q)",
    "D62": "cong(A, B, P, Q) :- contri(A, B, C, P, Q, R)",
    "D65": "eqratio(O, A, A, C, O, B, B, D) :- para(A, B, C, D), coll(O, A, C), coll(O, B, D)",
    "D68": "cong(A, B, A, C) :- midp(A, B, C)",
    "D70": "eqratio(M, A, A, B, N, C, C, D) :- midp(M, A, B), midp(N, C, D)",
    # Use this rule to generate eqangle from two perp facts. (Written by myself)
    "D76": "eqangle(k, l, m, n) :- perp(k, l), perp(m ,n)",
    "D77": "perp(m, n) :-  eqangle(k, l, m, n), perp(k, l)",
    "D78": "eqangle(l, k, m, n) :- perp(k, l), perp(m, n)",
    # TODO: Check if D79 to D89 is necessary.
    # The original version of ruleset does not use any rule to directly obtain contri, instead,
    # it uses D61 to obtain contri from a simtri and a cong fact.
    # To obtain simtri we need two eqangle facts (two groups of congruent angles),
    # so we are using two eqangle facts and one cong fact to obtain contri (ASA and AAS are not needed anymore),
    # but there exists methods to obtain contri by more than one cong and less than two eqangle facts (SAS and SSS).
    # They have been added to the ruleset additionally.
    # 4 rules for obtaining contri.
    "D79": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F), cong(B, C, E, F)",  # SAS
    "D80": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), cong(B, C, E, F), cong(A, C, D, F)",  # SSS
    # "D81": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F),"
    #        "eqangle(B, A, A, C, E, D, D, F)",  # ASA
    # "D82": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F),"
    #        "eqangle(A, C, C, B, D, F, F, E)",  # AAS
    # Get eqangle from contri.
    "D83": "eqangle(A, B, B, C, D, E, E, F) :- contri(A, B, C, D, E, F)",
    # Obtaining contri from two triangles that have an identical side.
    "D84":  "contri(A, B, C, D, B, C) :- cong(A, B, D, B), eqangle(A, B, B, C, D, E, E, F)",  # SAS
    "D85":  "contri(A, B, C, D, B, C) :- cong(A, B, D, B), cong(C, A, C, D)",  # SSS
    # "D86":  "contri(A, B, C, D, B, C) :- eqangle(A, B, B, C, D, B, B, C), eqangle(A, C, C, B, D, C, C, B)",  # ASA
    # "D87":  "contri(A, B, C, D, B, C) :- eqangle(A, B, B, C, D, B, B, C), eqangle(B, A, A, C, B, D, D, C)",  # AAS
    # D88 and D89 are using different sides of a triangle compares to D58.
    "D88": "simtri(A, B, C, P, Q, R) :- eqangle(A, B, B, C, P, Q, Q, R), eqangle(B, A, A, C, Q, P, P, R)",
    "D89": "simtri(A, B, C, P, Q, R) :- eqangle(A, C, B, C, P, R, Q, R), eqangle(B, A, A, C, Q, P, P, R)",
}

ruleset = dict()
for name, s in ruleset_raw.items():
    ruleset[name] = parser.parse_rule(s)
