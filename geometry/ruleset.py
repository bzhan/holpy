"""Set of rules."""

from geometry.expr import Fact, Rule
from geometry import parser

ruleset_raw = {
    # "D1": "coll(A, C, B) :- coll(A, B, C)",#
    # "D2": "coll(B, A, C) :- coll(A, B, C)",#
    # "D3": "coll(C, D, A) :- coll(A, B, C), coll(A, B, D)",#
    # "D4": "para(A, B, D, C):−para(A, B, C, D)", #
    "D5": "para(m, l) :- para(l, m)",
    "D6": "para(l, n) :- para(l, m), para(m, n)",
    "D8": "perp(m, l) :- perp(l, m)",
    "D9": "para(l, n) :- perp(l, m), perp(m, n)",
    # "D10": "perp(l, n) :- para(l, m), perp(m, n)",#
    # "D11": "midp(M, A, B) :- midp(M, B, A)", #
    # "D12": "circle(O, A, B, C) :- cong(O, A, O, B), cong(O, A, O, C)",#
    "D13": "cyclic(A, B, C, D) :- cong(O, A, O, B), cong(O, A, O, C), cong(O, A, O, D)",
    # "D17": "cyclic(B, C, D, E) :- cyclic(A, B, C, D), cyclic(A, B, C, E)",#
    # Currently no need
    # "D18": "eqangle(B, A, l, m ,n) :- eqangle(A, B, l, m, n)",#
    # "D19": "eqangle(l, k, n, m) :- eqangle(k, l, m, n)",#
    # "D20": "eqangle(m ,n ,k ,l) :- eqangle(k, l ,m ,n)",#
    "D21": "eqangle(k, m ,l, n) :- eqangle(k, l, m, n)",
    "D22": "eqangle(a, b, e, f) :- eqangle(a, b, c, d), eqangle(c, d, e, f)",#
    # "D23": "cong(A, B, D, C) :- cong(A, B, C, D)",#
    # "D24": "cong(C, D, A, B) :- cong(A, B, C, D)",#
    # "D25": "cong(A, B, E, F) :- cong(A, B, C, D), cong(C, D, E, F)",#
    "D28": "eqratio(m, n, k, l) :- eqratio(k, l, m, n)",
    "D29": "eqratio(k, m ,l, n) :- eqratio(k, l, m, n)",
    "D30": "eqratio(k, l, p, q) :- eqratio(k, l, m, n), eqratio(m, n, p, q)",
    "D33": "simtri(A, B, C, P, Q, R) :- simtri(P, Q, R, A, B, C)",
    "D34": "simtri(A, B, C, P, Q, R) :- simtri(A, B, C, E, F, G), simtri(E, F, G, P, Q, R)",
    "D37": "contri(A, B, C, P, Q, R) :- contri(P, Q, R, A, B, C)",
    "D38": "contri(A, B, C, P, Q, R) :- contri(A, B, C, E, F, G), contri(E, F, G, P, Q, R)",
    "D39": "para(a, b) :- eqangle(a, c, b, c)",
    "D40": "eqangle(a, c, b, c) :- para(a, b)",
    "D41": "eqangle(P, A, P, B, Q, A, Q, B) :- cyclic(A, B, P, Q)",
    "D42": "cyclic(A, B, P, Q) :- eqangle(P, A, P, B, Q, A, Q, B), ¬coll(P, Q, A, B)",
    "D43": "cong(A, B, P, Q) :- eqangle(C, A, C, B, R, P, R, Q), cyclic(A, B, C, P, Q, R)",
    "D44": "para(E, F, B, C) :- midp(E, A, B), midp(F, A, C)",
    "D45": "midp(F, A, C) :- midp(E, A, B), para(E, F, B, C), coll(F, A, C)",
    "D46": "eqangle(O, A, A, B, A, B, O, B) :- cong(O, A, O, B)",
    "D47": "cong(O, A, O, B) :- eqangle(O, A, A, B, A, B, O, B), ¬coll(O, A, B)",
    "D48": "eqangle(A, X, A, B, C, A, C, B) :- perp(O, A, A, X), circle(O, A, B, C)",
    "D49": "perp(O, A, A, X) :- eqangle(A, X, A, B, C, A, C, B), circle(O, A, B, C)",
    "D50": "eqangle(A, B, A, C, O, B, O, M) :- midp(M, B, C), circle(O, A, B, C)",
    "D51": "midp(M, B, C) :- coll(M, B, C), eqangle(A, B, A, C, O, B, O, M), circle(O, A, B, C)",
    "D52": "cong(A, M, B, M) :- perp(A, B, B, C), midp(M, A, C)",
    "D53": "perp(A, B, B, C) :- circle(O, A, B, C), coll(O, A, C)",
    "D54": "eqangle(A, D, C, D, C, D, C, B) :- para(A, B, C, D), cyclic(A, B, C, D)",
    "D55": "cong(O, A, O, B) :- midp(M, A, B), perp(O, M, A, B)",
    "D56": "perp(A, B, P, Q) :- cong(A, P, B, P), cong(A, Q, B, Q)",
    "D57": "perp(P, A, A, Q) :- cong(A, P, B, P), cong(A, Q, B, Q), cyclic(A, B, P, Q)",
    "D58": "simtri(A, B, C, P, Q, R) :- eqangle(A, B, B, C, P, Q, Q, R), eqangle(A, C, B, C, P, R, Q, R), ¬coll(A, B, C)",
    "D59": "eqratio(A, B, A, C, P, Q, P, R) :- simtri(A, B, C, P, Q, R)",
    "D60": "eqangle(A, B, B, C, P,Q, Q, R) :- simtri(A, B, C, P, Q, R)",
    "D61": "contri(A, B, C, P, Q, R) :- simtri(A, B, C, P, Q, R), cong(A, B, P, Q)",
    "D62": "cong(A, B, P, Q) :- contri(A, B, C, P, Q, R)",
    "D63": "para(A, C, B, D) :- midp(M, A, B), midp(M, C, D)",
    "D64": "midp(M, C, D) :- midp(M, A, B), para(A, C, B, D), para(A, D, B, C)",
    "D65": "eqratio(O, A, A, C, O, B, B, D) :- para(A, B, C, D), coll(O, A, C), coll(O, B, D)", #
    "D66": "coll(A, B, C) :- para(A, B, A, C)",
    "D67": "midp(A, B, C) :- cong(A, B, A, C), coll(A, B, C)",
    "D68": "cong(A, B, A, C) :- midp(A, B, C)",
    "D69": "coll(A, B, C) :- midp(A, B, C)",
    "D70": "eqratio(M, A, A, B, N, C, C, D) :- midp(M, A, B), midp(N, C, D)",
    # "D71": "perp(A, B, C, D) :- eqangle(A, B, C, D, C, D, A, B), ¬para(A, B, C, D)",
    # "D72": "para(A, B, C, D) :- eqangle(A, B, C, D, C, D, A, B), ¬perp(A, B, C, D)",
    # "D73": "para(A, B, C, D) :- eqangle(A, B, C, D, P, Q, U, V), para(P, Q, U, V)",
    # "D74": "perp(A, B, C, D) :- eqangle(A, B, C, D, P, Q, U, V), perp(P, Q, U, V)",
    # "D75": "cong(A, B, C, D) :- eqratio(A, B, C, D, P, Q, U, V), cong(P, Q, U, V)",
    "D71": "perp(a, b) :- eqangle(a, b, b, a), ¬para(a, b)",
    "D72": "para(a, b) :- eqangle(a, b, b, a), ¬perp(a, b)",
    "D73": "para(a, b) :- eqangle(a, b, c, d), para(c, d)",
    "D74": "perp(a, b) :- eqangle(a, b, c, d), perp(c, d)",
    "D75": "cong(a, b) :- eqratio(a, b, c, d), cong(c, d)",

    # ⬇ Additional rules ⬇ #
    # Use this rule to generate eqangle from two perp facts. (Written by myself)
    "D76": "eqangle(k, l, m, n) :- perp(k, l), perp(m ,n)",
    "D77": "perp(m, n) :- eqangle(k, l, m, n), perp(k, l)",
    "D78": "eqangle(l, k, m, n) :- perp(k, l), perp(m, n)",
    # TODO: Check if D79 to D89 is necessary.
    # The original version of ruleset does not use any rule to directly obtain contri, instead,
    # it uses D61 to obtain contri from a simtri and a cong fact.
    # To obtain simtri we need two eqangle facts (two groups of congruent angles),
    # so we are using two eqangle facts and one cong fact to obtain contri (ASA and AAS are not needed anymore),
    # but there exists methods to obtain contri by more than one cong and less than two eqangle facts (SAS and SSS).
    # They have been added to the ruleset additionally.
    # 4 rules for obtaining contri.
    # "D79": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F), cong(B, C, E, F)",  # SAS
    # "D80": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), cong(B, C, E, F), cong(A, C, D, F)",  # SSS
    # "D81": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F),"
    #        "eqangle(B, A, A, C, E, D, D, F)",  # ASA
    # "D82": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F),"
    #        "eqangle(A, C, C, B, D, F, F, E)",  # AAS
    # Get eqangle from contri.
    "D83": "eqangle(A, B, B, C, D, E, E, F) :- contri(A, B, C, D, E, F)",
    # Obtaining contri from two triangles that have an identical side.
    # "D84": "contri(A, B, C, D, B, C) :- cong(A, B, D, B), eqangle(A, B, B, C, B, C, D, B)",  # SAS
    # "D85":  "contri(A, B, C, D, B, C) :- cong(A, B, D, B), cong(C, A, C, D)",  # SSS
    # "D86":  "contri(A, B, C, D, B, C) :- eqangle(A, B, B, C, D, B, B, C), eqangle(A, C, C, B, D, C, C, B)",  # ASA
    # "D87":  "contri(A, B, C, D, B, C) :- eqangle(A, B, B, C, D, B, B, C), eqangle(B, A, A, C, B, D, D, C)",  # AAS
    # D88 and D89 are using different sides of a triangle compares to D58.
    "D88": "simtri(A, B, C, P, Q, R) :- eqangle(A, B, B, C, P, Q, Q, R), eqangle(B, A, A, C, Q, P, P, R), ¬coll(A, B, C)",
    "D89": "simtri(A, B, C, P, Q, R) :- eqangle(A, C, C, B, Q, R, P, R), eqangle(B, A, A, C, R, P, P, Q), ¬coll(A, B, C)",

    "D90": "eqangle(c, a, c, b) :- para(a, b)",
    "D91": "cong(O, A, O, B) :- circle(O, A, B, C)",
}

ruleset = dict()
for name, s in ruleset_raw.items():
    ruleset[name] = parser.parse_rule(s)


ruleset_raw_reduced = {
    # "D1": "coll(A, C, B) :- coll(A, B, C)",
    # "D2": "coll(B, A, C) :- coll(A, B, C)",
    # "D3": "coll(C, D, A) :- coll(A, B, C), coll(A, B, D)",
    "D5": "para(m, l) :- para(l, m)",
    "D6": "para(l, n) :- para(l, m), para(m, n)",
    "D8": "perp(m, l) :- perp(l, m)",
    "D9": "para(l, n) :- perp(l, m), perp(m, n)",
    # "D10": "perp(l, n) :- para(l, m), perp(m, n)",
    # "D12": "circle(O, A, B, C) :- cong(O, A, O, B), cong(O, A, O, C)",
    "D13": "cyclic(A, B, C, D) :- cong(O, A, O, B), cong(O, A, O, C), cong(O, A, O, D)",
    # "D17": "cyclic(B, C, D, E) :- cyclic(A, B, C, D), cyclic(A, B, C, E)",
    # Currently no need
    # "D18": "eqangle(B, A, l, m ,n) :- eqangle(A, B, l, m, n)",
    # "D19": "eqangle(l, k, n, m) :- eqangle(k, l, m, n)",
    # "D20": "eqangle(m ,n ,k ,l) :- eqangle(k, l ,m ,n)",
    "D21": "eqangle(k, m ,l, n) :- eqangle(k, l, m, n)",
    # "D22": "eqangle(a, b, e, f) :- eqangle(a, b, c, d), eqangle(c, d, e, f)",
    # "D24": "cong(C, D, A, B) :- cong(A, B, C, D)",
    # "D25": "cong(A, B, E, F) :- cong(A, B, C, D), cong(C, D, E, F)",
    # "D29": "eqratio(k, m ,l, n) :- eqratio(k, l, m, n)",
    # "D30": "eqratio(k, l, p, q) :- eqratio(k, l, m, n), eqratio(m, n, p, q)",
    # "D39": "para(A, B, C, D) :- eqangle(A, B, P, Q, C, D, P, Q)",
    "D40": "eqangle(a, c, b, c) :- para(a, b)",
    "D41": "eqangle(P, A, P, B, Q, A, Q, B) :- cyclic(A, B, P, Q)",
    "D42": "cyclic(A, B, P, Q) :- eqangle(P, A, P, B, Q, A, Q, B), ¬coll(P, Q, A, B)",
    # Match facts that are not "cyclic" or "circle" first. The order of arguments in D43 differ from the
    # original version.
    "D43": "cong(A, B, P, Q) :- eqangle(C, A, C, B, R, P, R, Q), cyclic(A, B, C, P, Q, R)",
    "D44": "para(E, F, B, C) :- midp(E, A, B), midp(F, A, C)",
    # "D45": "midp(F, A, C) :- midp(E, A, B), para(E, F, B, C)",
    "D45": "midp(F, A, C) :- midp(E, A, B), para(E, F, B, C), coll(F, A, C)",
    "D46": "eqangle(O, A, A, B, A, B, O, B) :- cong(O, A, O, B)",
    # "D47": "cong(O, A, O, B) :- eqangle(O, A, A, B, A, B, O, B), ¬coll(O, A, B)",
    # "D48": "eqangle(A, X, A, B, C, A, C, B) :- perp(O, A, A, X), circle(O, A, B, C)",
    # "D49": "perp(O, A, A, X) :- eqangle(A, X, A, B, C, A, C, B), circle(O, A, B, C)",
    # "D50": "eqangle(A, B, A, C, O, B, O, M) :- midp(M, B, C), circle(O, A, B, C)",
    # "D51": "midp(M, B, C) :- coll(M, B, C), eqangle(A, B, A, C, O, B, O, M), circle(O, A, B, C)",
    # "D52": "cong(A, M, B, M) :- perp(A, B, B, C), midp(M, A, C)",
    "D53": "perp(A, B, B, C) :- circle(O, A, B, C), coll(O, A, C)",
    # "D54": "eqangle(A, D, C, D, C, D, C, B) :- para(A, B, C, D), cyclic(A, B, C, D)",
    # "D55": "cong(O, A, O, B) :- midp(M, A, B), perp(O, M, A, B)",
    "D56": "perp(A, B, P, Q) :- cong(A, P, B, P), cong(A, Q, B, Q)",
    "D57": "perp(P, A, A, Q) :- cong(A, P, B, P), cong(A, Q, B, Q), cyclic(A, B, P, Q)",
    "D58": "simtri(A, B, C, P, Q, R) :- eqangle(A, B, B, C, P, Q, Q, R), eqangle(A, C, B, C, P, R, Q, R), ¬coll(A, B, C)",
    "D59": "eqratio(A, B, A, C, P, Q, P, R) :- simtri(A, B, C, P, Q, R)",
    # "D60": "eqangle(A, B, B, C, P, Q, Q, R) :- simtri(A, B, C, P, Q, R)",
    "D61": "contri(A, B, C, P, Q, R) :- simtri(A, B, C, P, Q, R), cong(A, B, P, Q)",
    "D62": "cong(A, B, P, Q) :- contri(A, B, C, P, Q, R)",
    # "D63": "para(A, C, B, D) :- midp(M, A, B), midp(M, C, D)",
    # "D64": "midp(M, C, D) :- midp(M, A, B), para(A, C, B, D), para(A, D, B, C)",
    # "D65": "eqratio(O, A, A, C, O, B, B, D) :- para(A, B, C, D), coll(O, A, C), coll(O, B, D)", #
    "D66": "coll(A, B, C) :- para(A, B, A, C)",
    # "D67": "midp(A, B, C) :- cong(A, B, A, C), coll(A, B, C)",
    "D68": "cong(A, B, A, C) :- midp(A, B, C)",
    "D69": "coll(A, B, C) :- midp(A, B, C)",
    "D70": "eqratio(M, A, A, B, N, C, C, D) :- midp(M, A, B), midp(N, C, D)",
    # "D71": "perp(A, B, C, D) :- eqangle(A, B, C, D, C, D, A, B), ¬para(A, B, C, D)",
    # "D72": "para(A, B, C, D) :- eqangle(A, B, C, D, C, D, A, B), ¬perp(A, B, C, D)",
    # "D73": "para(A, B, C, D) :- eqangle(A, B, C, D, P, Q, U, V), para(P, Q, U, V)",
    # "D74": "perp(A, B, C, D) :- eqangle(A, B, C, D, P, Q, U, V), perp(P, Q, U, V)",
    # "D75": "cong(A, B, C, D) :- eqratio(A, B, C, D, P, Q, U, V), cong(P, Q, U, V)",
    "D71": "perp(a, b) :- eqangle(a, b, b, a), ¬para(a, b)",
    "D72": "para(a, b) :- eqangle(a, b, b, a), ¬perp(a, b)",
    "D73": "para(a, b) :- eqangle(a, b, c, d), para(c, d)",
    "D74": "perp(a, b) :- eqangle(a, b, c, d), perp(c, d)",
    "D75": "cong(a, b) :- eqratio(a, b, c, d), cong(c, d)",

    # ⬇ Additional rules ⬇ #
    # Use this rule to generate eqangle from two perp facts. (Written by myself)
    "D76": "eqangle(k, l, m, n) :- perp(k, l), perp(m ,n)",
    "D77": "perp(m, n) :- eqangle(k, l, m, n), perp(k, l)",
    "D78": "eqangle(l, k, m, n) :- perp(k, l), perp(m, n)",
    # TODO: Check if D79 to D89 is necessary.
    # The original version of ruleset does not use any rule to directly obtain contri, instead,
    # it uses D61 to obtain contri from a simtri and a cong fact.
    # To obtain simtri we need two eqangle facts (two groups of congruent angles),
    # so we are using two eqangle facts and one cong fact to obtain contri (ASA and AAS are not needed anymore),
    # but there exists methods to obtain contri by more than one cong and less than two eqangle facts (SAS and SSS).
    # They have been added to the ruleset additionally.
    # 4 rules for obtaining contri.
    # "D79": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F), cong(B, C, E, F)",  # SAS
    # "D80": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), cong(B, C, E, F), cong(A, C, D, F)",  # SSS
    # "D81": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F),"
    #        "eqangle(B, A, A, C, E, D, D, F)",  # ASA
    # "D82": "contri(A, B, C, D, E, F) :- cong(A, B, D, E), eqangle(A, B, B, C, D, E, E, F),"
    #        "eqangle(A, C, C, B, D, F, F, E)",  # AAS
    # Get eqangle from contri.
    "D83": "eqangle(A, B, B, C, D, E, E, F) :- contri(A, B, C, D, E, F)",
    # Obtaining contri from two triangles that have an identical side.
    # "D84":  "contri(A, B, C, D, B, C) :- cong(A, B, D, B), eqangle(A, B, B, C, B, C, D, B)",  # SAS
    # "D85":  "contri(A, B, C, D, B, C) :- cong(A, B, D, B), cong(C, A, C, D)",  # SSS
    # "D86":  "contri(A, B, C, D, B, C) :- eqangle(A, B, B, C, D, B, B, C), eqangle(A, C, C, B, D, C, C, B)",  # ASA
    # "D87":  "contri(A, B, C, D, B, C) :- eqangle(A, B, B, C, D, B, B, C), eqangle(B, A, A, C, B, D, D, C)",  # AAS
    # D88 and D89 are using different sides of a triangle compares to D58.
    "D88": "simtri(A, B, C, P, Q, R) :- eqangle(A, B, B, C, P, Q, Q, R), eqangle(B, A, A, C, Q, P, P, R), ¬coll(A, B, C)",
    "D89": "simtri(A, B, C, P, Q, R) :- eqangle(A, C, C, B, Q, R, P, R), eqangle(B, A, A, C, R, P, P, Q), ¬coll(A, B, C)",

    "D90": "eqangle(c, a, c, b) :- para(a, b)",
}
ruleset_reduced = dict()
for name, s in ruleset_raw_reduced.items():
    ruleset_reduced[name] = parser.parse_rule(s)