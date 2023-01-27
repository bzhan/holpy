"""Context of integral calculations"""

from typing import Optional, List
import os
import json

from integral.expr import Var, Symbol, Expr, expr_to_pattern, match
from integral import parser
from integral.conditions import Conditions

dirname = os.path.dirname(__file__)

class IndefiniteIntegralIdentity:
    def __init__(self, lhs: Expr, rhs: Expr, *, conds: Optional[Conditions] = None, simp_level: int = 1):
        self.lhs = lhs
        self.rhs = rhs
        self.conds = conds
        self.simp_level = simp_level

    def __str__(self):
        return "%s => %s" % (self.lhs, self.rhs)


class Context:
    def __init__(self):
        self.indefinite_integrals: List[IndefiniteIntegralIdentity] = list()

    def __str__(self):
        res = ""
        res += "Indefinite integrals\n"
        for indef in self.indefinite_integrals:
            res += str(indef) + "\n"
        return res

    def add_indefinite_integral(self, eq: Expr):
        if not (eq.is_equals() and eq.lhs.is_indefinite_integral()):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.indefinite_integrals.append(IndefiniteIntegralIdentity(symb_lhs, symb_rhs))

    def load_book(self, content):
        if isinstance(content, str):
            filename = os.path.join(dirname, "../integral/examples/" + content + '.json')
            with open(filename, 'r', encoding='utf-8') as f:
                content = json.load(f)['content']

        for item in content:
            if item['type'] == 'axiom' or item['type'] == 'problem':
                e = parser.parse_expr(item['expr'])
                if e.is_equals() and e.lhs.is_indefinite_integral():
                    self.add_indefinite_integral(e)

    def apply_indefinite_integral(self, e: Expr) -> Expr:
        for indef in self.indefinite_integrals:
            inst = match(e, indef.lhs)
            if inst is None:
                continue
            inst['x'] = Var(e.var)
            return indef.rhs.inst_pat(inst)
