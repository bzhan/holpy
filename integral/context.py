"""Context of integral calculations"""

from typing import Optional, List, Dict
import os
import json

from integral.expr import Var, Expr, expr_to_pattern, match
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
    """Maintains the current context of calculation.
    
    Information kept in context include the following:
    
    - List of existing identities (for indefinite integrals, definite integrals,
      trigonometric identities, etc).
      
    - Assumptions for the current computation.
    
    - List of variable substitutions.

    """
    def __init__(self, parent: Optional["Context"] = None):
        # Parent context
        self.parent = parent

        # List of indefinite integral identities
        self.indefinite_integrals: List[IndefiniteIntegralIdentity] = list()

        # List of assumptions
        self.conds: Conditions = Conditions()

        # List of substitutions
        self.substs: Dict[str, Expr] = dict()

    def __str__(self):
        res = ""
        res += "Indefinite integrals\n"
        for indef in self.indefinite_integrals:
            res += str(indef) + "\n"
        res += "Conditions\n"
        for name, cond in self.conds.data.items():
            res += "%s: %s\n" % (name, cond)
        return res
    
    def get_indefinite_integrals(self) -> List[IndefiniteIntegralIdentity]:
        res = self.parent.get_indefinite_integrals() if self.parent is not None else []
        res.extend(self.indefinite_integrals)
        return res
    
    def get_conds(self) -> Conditions:
        res = self.parent.get_conds() if self.parent is not None else Conditions()
        for name, cond in self.conds.data.items():
            res.add_condition(name, cond)
        return res

    def add_indefinite_integral(self, eq: Expr):
        if not (eq.is_equals() and eq.lhs.is_indefinite_integral()):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.indefinite_integrals.append(IndefiniteIntegralIdentity(symb_lhs, symb_rhs))

    def add_condition(self, name: str, cond: Expr):
        self.conds.add_condition(name, cond)

    def extend_condition(self, conds: Conditions):
        for name, cond in conds.data.items():
            self.add_condition(name, cond)

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
        for indef in self.get_indefinite_integrals():
            inst = match(e, indef.lhs)
            if inst is None:
                continue
            inst['x'] = Var(e.var)
            return indef.rhs.inst_pat(inst)

        # No matching identity found
        return e
