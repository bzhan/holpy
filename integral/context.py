"""Context of integral calculations"""

from typing import Optional, List, Dict
import os
import json

from integral.expr import Var, Expr, expr_to_pattern, match
from integral import parser
from integral.conditions import Conditions

dirname = os.path.dirname(__file__)

class Identity:
    def __init__(self, lhs: Expr, rhs: Expr, *,
                 conds: Optional[Conditions] = None, simp_level: int = 1, category: str = ""):
        self.lhs = lhs
        self.rhs = rhs
        self.conds = conds
        self.simp_level = simp_level
        self.category = category

    def __str__(self):
        if self.category != "":
            return "%s => %s  (%s)" % (self.lhs, self.rhs, self.category)
        else:
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
        self.indefinite_integrals: List[Identity] = list()

        # List of definite integral identities
        self.definite_integrals: List[Identity] = list()

        # List of series expansions
        self.series_expansions: List[Identity] = list()

        # List of series evaluations
        self.series_evaluations: List[Identity] = list()

        # List of other identities (trigonometric, etc)
        self.other_identities: List[Identity] = list()

        # List of assumptions
        self.conds: Conditions = Conditions()

        # List of substitutions
        self.substs: Dict[str, Expr] = dict()

    def __str__(self):
        res = ""
        res += "Indefinite integrals\n"
        for identity in self.indefinite_integrals:
            res += str(identity) + "\n"
        res += "Definite integrals\n"
        for identity in self.definite_integrals:
            res += str(identity) + "\n"
        res += "Series expansions\n"
        for identity in self.series_expansions:
            res += str(identity) + "\n"
        res += "Series evaluations\n"
        for identity in self.series_evaluations:
            res += str(identity) + "\n"
        res += "Other identities\n"
        for identity in self.other_identities:
            res += str(identity) + "\n"
        res += "Conditions\n"
        for cond in self.conds.data:
            res += str(cond) + "\n"
        return res
    
    def get_indefinite_integrals(self) -> List[Identity]:
        res = self.parent.get_indefinite_integrals() if self.parent is not None else []
        res.extend(self.indefinite_integrals)
        return res
    
    def get_definite_integrals(self) -> List[Identity]:
        res = self.parent.get_definite_integrals() if self.parent is not None else []
        res.extend(self.definite_integrals)
        return res

    def get_series_expansions(self) -> List[Identity]:
        res = self.parent.get_series_expansions() if self.parent is not None else []
        res.extend(self.series_expansions)
        return res

    def get_series_evaluations(self) -> List[Identity]:
        res = self.parent.get_series_evaluations() if self.parent is not None else []
        res.extend(self.series_evaluations)
        return res

    def get_other_identities(self) -> List[Identity]:
        res = self.parent.get_other_identities() if self.parent is not None else []
        res.extend(self.other_identities)
        return res

    def get_conds(self) -> Conditions:
        res = self.parent.get_conds() if self.parent is not None else Conditions()
        for cond in self.conds.data:
            res.add_condition(cond)
        return res
    
    def get_substs(self) -> Dict[str, Expr]:
        res = self.parent.get_substs() if self.parent is not None else dict()
        for var, expr in self.substs.items():
            res[var] = expr
        return res

    def add_indefinite_integral(self, eq: Expr):
        if not (eq.is_equals() and eq.lhs.is_indefinite_integral()):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.indefinite_integrals.append(Identity(symb_lhs, symb_rhs))

    def add_definite_integral(self, eq: Expr):
        if not (eq.is_equals() and eq.lhs.is_integral()):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.definite_integrals.append(Identity(symb_lhs, symb_rhs))

    def add_series_expansion(self, eq: Expr):
        if not (eq.is_equals() and not eq.lhs.is_summation() and eq.rhs.is_summation()):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.series_expansions.append(Identity(symb_lhs, symb_rhs))

    def add_series_evaluation(self, eq: Expr):
        if not (eq.is_equals() and eq.lhs.is_summation() and not eq.rhs.is_summation()):
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.series_evaluations.append(Identity(symb_lhs, symb_rhs))

    def add_other_identities(self, eq: Expr, category: str):
        if not eq.is_equals():
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.other_identities.append(Identity(symb_lhs, symb_rhs, category=category))

    def add_condition(self, cond: Expr):
        self.conds.add_condition(cond)

    def extend_condition(self, conds: Conditions):
        for cond in conds.data:
            self.add_condition(cond)

    def add_subst(self, var: str, expr: Expr):
        self.substs[var] = expr

    def extend_substs(self, substs: Dict[str, Expr]):
        for var, expr in substs.items():
            self.substs[var] = expr

    def load_book(self, content, upto: Optional[str] = None):
        if isinstance(content, str):
            filename = os.path.join(dirname, "../integral/examples/" + content + '.json')
            with open(filename, 'r', encoding='utf-8') as f:
                content = json.load(f)['content']

        for item in content:
            if upto is not None and "path" in item and item['path'] == upto:
                break
            if item['type'] == 'axiom' or item['type'] == 'problem':
                e = parser.parse_expr(item['expr'])
                if e.is_equals() and e.lhs.is_indefinite_integral():
                    self.add_indefinite_integral(e)
                elif e.is_equals() and e.lhs.is_integral():
                    self.add_definite_integral(e)
                elif e.is_equals() and not e.lhs.is_summation() and e.rhs.is_summation():
                    self.add_series_expansion(e)
                elif e.is_equals() and e.lhs.is_summation() and not e.rhs.is_summation():
                    self.add_series_evaluation(e)
                elif e.is_equals() and 'category' in item:
                    self.add_other_identities(e, item['category'])

        return
