"""Set of rules."""

from geometry.expr import Fact, Rule
from geometry import parser

ruleset_raw = {
    "D1": "coll(A, C, B) :- coll(A, B, C)",
    "D2": "coll(B, A, C) :- coll(A, B, C)",
    "D3": "coll(C, D, A) :- coll(A, B, C), coll(A, B, D)",
}

ruleset = dict()
for name, s in ruleset_raw.items():
    ruleset[name] = parser.parse_rule(s)
