"""Context of integral calculations"""

from typing import Optional, List, Dict
import os
import json

from integral.expr import Expr, expr_to_pattern
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
    
    - List of function definitions

    - List of existing identities (for indefinite integrals, definite integrals,
      trigonometric identities, etc).
      
    - Assumptions for the current computation.
    
    - List of variable substitutions.

    """
    def __init__(self, parent: Optional["Context"] = None):
        # Parent context
        self.parent = parent

        # List of definitions
        self.definitions: List[Identity] = list()

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

        # List of simplification rules
        self.simp_identities: List[Identity] = list()

        # List of tables of function values
        self.function_tables: Dict[str, Dict[Expr, Expr]] = dict()

        # Lemmas
        self.lemmas: List[Identity] = list()

        # Inductive hypothesis
        self.induct_hyps: List[Identity] = list()

        # List of assumptions
        self.conds: Conditions = Conditions()

        # List of substitutions
        self.substs: Dict[str, Expr] = dict()

    def __str__(self):
        res = ""
        res += "Definitions\n"
        for identity in self.get_definitions():
            res += str(identity) + "\n"
        res += "Indefinite integrals\n"
        for identity in self.get_indefinite_integrals():
            res += str(identity) + "\n"
        res += "Definite integrals\n"
        for identity in self.get_definite_integrals():
            res += str(identity) + "\n"
        res += "Series expansions\n"
        for identity in self.get_series_expansions():
            res += str(identity) + "\n"
        res += "Series evaluations\n"
        for identity in self.get_series_evaluations():
            res += str(identity) + "\n"
        res += "Other identities\n"
        for identity in self.get_other_identities():
            res += str(identity) + "\n"
        res += "Simplification rules\n"
        for identity in self.get_simp_identities():
            res += str(identity) + "\n"
        res += "Function tables\n"
        for funcname in self.get_function_tables():
            res += "  table for %s\n" % funcname
        res += "Lemmas\n"
        for identity in self.get_lemmas():
            res += str(identity) + "\n"
        res += "Inductive hypothesis\n"
        for identity in self.get_induct_hyps():
            res += str(identity) + "\n"
        res += "Conditions\n"
        for cond in self.get_conds().data:
            res += str(cond) + "\n"
        return res
    
    def get_definitions(self) -> List[Identity]:
        res = self.parent.get_definitions() if self.parent is not None else []
        res.extend(self.definitions)
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
    
    def get_simp_identities(self) -> List[Identity]:
        res = self.parent.get_simp_identities() if self.parent is not None else []
        res.extend(self.simp_identities)
        return res

    def get_function_tables(self) -> Dict[str, Dict[Expr, Expr]]:
        res = self.parent.get_function_tables() if self.parent is not None else dict()
        res.update(self.function_tables)
        return res

    def get_lemmas(self) -> List[Identity]:
        res = self.parent.get_lemmas() if self.parent is not None else []
        res.extend(self.lemmas)
        return res

    def get_induct_hyps(self) -> List[Identity]:
        res = self.parent.get_induct_hyps() if self.parent is not None else []
        res.extend(self.induct_hyps)
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

    def add_definition(self, eq: Expr):
        if not eq.is_equals():
            raise TypeError

        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.definitions.append(Identity(symb_lhs, symb_rhs))

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

    def add_other_identities(self, eq: Expr, category: str, attributes: Optional[List[str]] = None):
        if not eq.is_equals():
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.other_identities.append(Identity(symb_lhs, symb_rhs, category=category))
        if attributes is not None and 'bidirectional' in attributes:
            self.other_identities.append(Identity(symb_rhs, symb_lhs, category=category))

    def add_simp_identity(self, eq: Expr, conds: Conditions):
        if not eq.is_equals():
            raise TypeError
        
        symb_lhs = expr_to_pattern(eq.lhs)
        symb_rhs = expr_to_pattern(eq.rhs)
        self.simp_identities.append(Identity(symb_lhs, symb_rhs, conds=conds))

    def add_function_table(self, funcname: str, table: Dict[str, str]):
        self.function_tables[funcname] = dict()
        for input, output in table.items():
            input = parser.parse_expr(input)
            output = parser.parse_expr(output)
            self.function_tables[funcname][input] = output

    def add_lemma(self, eq: Expr):
        if not eq.is_equals():
            raise TypeError

        # Note: no conversion to symbols for lemmas within a file.        
        self.lemmas.append(Identity(eq.lhs, eq.rhs))

    def add_induct_hyp(self, eq: Expr):
        if not eq.is_equals():
            raise TypeError

        # Note: no conversion to symbols for inductive hypothesis        
        self.induct_hyps.append(Identity(eq.lhs, eq.rhs))

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

    def extend_by_item(self, item):
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
                self.add_other_identities(e, item['category'], item.get('attributes'))
        if 'attributes' in item and 'simplify' in item['attributes']:
            e = parser.parse_expr(item['expr'])
            conds = Conditions()
            if 'conds' in item:
                for cond in item['conds']:
                    conds.add_condition(parser.parse_expr(cond))
            self.add_simp_identity(e, conds)
        if item['type'] == 'definition':
            e = parser.parse_expr(item['expr'])
            self.add_definition(e)
        if item['type'] == 'table':
            self.add_function_table(item['name'], item['table'])
        if item['type'] == 'lemma':
            e = parser.parse_expr(item['expr'])
            self.add_lemma(e)

    def load_book(self, content, upto: Optional[str] = None):
        if isinstance(content, str):
            filename = os.path.join(dirname, "../integral/examples/" + content + '.json')
            with open(filename, 'r', encoding='utf-8') as f:
                content = json.load(f)['content']

        for item in content:
            if upto is not None and "path" in item and item['path'] == upto:
                break
            self.extend_by_item(item)

        return
