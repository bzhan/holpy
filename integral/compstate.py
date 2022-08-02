"""State of computation"""

from ast import Assert
from copy import copy
from msilib.schema import Condition
from typing import Optional, Tuple, Union

from integral.expr import Expr, Eq, Var, Const
from integral import rules, expr
from integral.rules import Rule
from integral.conditions import Conditions
from integral import conditions
from integral import latex
from integral import parser


class Label:
    def __init__(self, data):
        self.data = []
        if isinstance(data, str):
            split = data.split(".")
            for n in split:
                assert int(n) >= 1, "Label: non-positive value"
                self.data.append(int(n) - 1)
        elif isinstance(data, list):
            assert all(n >= 0 for n in data), "Label: negative value"
            self.data = list(data)
        else:
            raise AssertionError("Label: unexpected type")

    @property
    def head(self):
        return self.data[0]

    @property
    def tail(self):
        return Label(self.data[1:])

    def empty(self):
        return len(self.data) == 0

    def __str__(self):
        return ".".join(str(n + 1) for n in self.data)


class StateItem:
    """Items in a state of computation"""
    def export(self):
        """Obtain the JSON representation of the item."""
        raise NotImplementedError

    def get_by_label(self, label) -> "StateItem":
        """Return the object at the given label."""
        raise NotImplementedError

    def get_facts(self):
        """Return the list of facts in this item."""
        return []


class FuncDef(StateItem):
    """Introduce a new function definition."""
    def __init__(self, eq: Expr, conds: Optional[Conditions] = None):
        if not (eq.is_equals() and eq.lhs.is_fun()):
            raise AssertionError("FuncDef: left side should be a function")

        self.eq = eq
        self.symb = self.eq.lhs.func_name
        self.args = self.eq.lhs.args
        self.body = self.eq.rhs

        if any(not arg.is_var() for arg in self.args) or len(self.args) != len(set(self.args)):
            raise AssertionError("FuncDef: arguments should be distinct variables")

        if conds is None:
            conds = Conditions()
        self.conds = conds

    def __str__(self):
        res = "Definition\n"
        res += "  %s\n" % self.eq
        return res

    def export(self):
        res = {
            "type": "FuncDef",
            "eq": str(self.eq),
            "latex_lhs": latex.convert_expr(self.eq.lhs),
            "latex_eq": latex.convert_expr(self.eq)
        }
        if self.conds.data:
            res["conds"] = self.conds.export()
        return res

    def get_by_label(self, label: Label):
        if not label.empty():
            raise AssertionError("get_by_label: invalid label")
        return self

    def get_facts(self):
        return [self.eq]


class Goal(StateItem):
    """Goal to be proved."""
    def __init__(self, goal: Expr, conds: Optional[Conditions] = None):

        self.goal = goal
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.proof = None

    def __str__(self):
        if self.is_finished():
            res = "Goal (finished)\n"
        else:
            res = "Goal\n"
        res += "  %s\n" % self.goal
        res += str(self.proof)
        return res

    def is_finished(self):
        return self.proof is not None and self.proof.is_finished()

    def export(self):
        res = {
            "type": "Goal",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "finished": self.is_finished()
        }
        if self.proof:
            res['proof'] = self.proof.export()
        if self.conds.data:
            res['conds'] = self.conds.export()
        return res

    def proof_by_calculation(self):
        self.proof = CalculationProof(self.goal, conds=self.conds)
        return self.proof

    def proof_by_induction(self, induct_var: str, start:int=0):
        self.proof = InductionProof(self.goal, induct_var, conds=self.conds,start = start)
        return self.proof

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        else:
            if self.proof is None:
                raise AssertionError("get_by_label: goal %s has no proof" % str(self.goal))
            return self.proof.get_by_label(label)

    def get_facts(self):
        return [self.goal]


class CalculationStep(StateItem):
    """A step in the calculation."""
    def __init__(self, rule: Rule, res: Expr, parent: "Calculation", id: int):
        self.rule = rule
        self.res = res
        self.parent = parent
        self.id = id

    def __str__(self):
        return "%s (%s)" % (self.res, self.rule)

    def export(self):
        return {
            "type": "CalculationStep",
            "rule": self.rule.export(),
            "res": str(self.res),
            "latex_res": latex.convert_expr(self.res)
        }

    def perform_rule(self, rule: Rule):
        self.parent.perform_rule(rule, id=self.id)


class Calculation(StateItem):
    """Calculation starting from an expression.

    start: starting expression.
    conds: (optional) a list of conditions under which the calculation
        is carried out.

    """
    def __init__(self, start: Expr, *, conds: Optional[Conditions] = None):
        self.start = start
        self.steps = []
        if conds is None:
            conds = Conditions()
        self.conds = conds

    def __str__(self):
        res = "  " + str(self.start) + "\n"
        for step in self.steps:
            res += "= %s\n" % step
        return res

    def export(self):
        return {
            "type": "Calculation",
            "start": str(self.start),
            "latex_start": latex.convert_expr(self.start),
            "steps": [step.export() for step in self.steps]
        }

    def add_step(self, step: CalculationStep):
        """Add the given step to the computation."""
        self.steps.append(step)

    @property
    def last_expr(self) -> Expr:
        """Last expression of the calculation."""
        if self.steps:
            return self.steps[-1].res
        else:
            return self.start

    def perform_rule(self, rule: Rule, id: Optional[int] = None):
        """Perform the given rule on the current expression."""
        if id is not None:
            # Cut off later steps
            self.steps = self.steps[:id+1]
        else:
            id = len(self.steps) - 1

        e = self.last_expr
        new_e = rule.eval(e, conds=self.conds)
        self.add_step(CalculationStep(rule, new_e, self, id+1))

    def get_by_label(self, label: Label) -> "StateItem":
        if label.empty():
            return self
        elif label.tail.empty():
            return self.steps[label.head]
        else:
            raise AssertionError("get_by_label: invalid label")


class CalculationProof(StateItem):
    """Proof for an equation by calculation.
    
    The proof consists of calculation of left and right sides.

    """
    def __init__(self, goal: Expr, *, conds: Optional[Conditions] = None):
        if not goal.is_equals():
            raise AssertionError("CalculationProof: goal is not an equality.")

        self.goal = goal
        if conds is None:
            conds = Conditions()
        self.conds = conds

        self.lhs_calc = Calculation(self.goal.lhs, conds=self.conds)
        self.rhs_calc = Calculation(self.goal.rhs, conds=self.conds)

    def __str__(self):
        if self.is_finished():
            res = "Proof by calculation (finished)\n"
        else:
            res = "Proof by calculation\n"
        if self.lhs_calc.steps:
            res += "LHS:\n"
            res += str(self.lhs_calc)
        if self.rhs_calc.steps:
            res += "RHS:\n"
            res += str(self.rhs_calc)
        return res

    def is_finished(self):
        return self.lhs_calc.last_expr == self.rhs_calc.last_expr

    def export(self):
        return {
            "type": "CalculationProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "lhs_calc": self.lhs_calc.export(),
            "rhs_calc": self.rhs_calc.export(),
            "finished": self.is_finished()
        }

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        elif label.head == 0:
            return self.lhs_calc.get_by_label(label.tail)
        elif label.head == 1:
            return self.rhs_calc.get_by_label(label.tail)
        else:
            raise AssertionError("get_by_label: invalid label")


class InductionProof(StateItem):
    """Proof for an equation by induction on natural numbers.
    
    This breaks the equation goal into two goals, corresponding to the
    base case and inductive case.

    """
    def __init__(self, goal: Expr, induct_var: str, *, conds: Optional[Conditions] = None, start = Const(0)):
        if not goal.is_equals():
            print(str(goal))
            raise AssertionError("InductionProof: currently only support equation goals.")

        self.goal = goal
        self.induct_var = induct_var
        if conds is None:
            conds = Conditions()
        self.conds = conds
        self.start = Const(start)
        # Base case: n = 0
        eq0 = goal.subst(induct_var, self.start).normalize()
        self.base_case = Goal(eq0, conds=self.conds)
        
        # Inductive case:
        eqI = goal.subst(induct_var, Var(induct_var) + 1).normalize()
        induct_conds = copy(self.conds)
        induct_conds.add_condition("IH", self.goal)
        self.induct_case = Goal(eqI, conds=induct_conds)

    def __str__(self):
        if self.is_finished():
            res = "Proof by induction on %s (finished)\n" % self.induct_var
        else:
            res = "Proof by induction on %s\n" % self.induct_var
        res += "Base case: %s\n" % self.base_case.goal
        res += str(self.base_case)
        res += "Induct case: %s\n" % self.induct_case.goal
        res += str(self.induct_case)
        return res

    def is_finished(self):
        return self.base_case.is_finished() and self.induct_case.is_finished()

    def export(self):
        return {
            "type": "InductionProof",
            "goal": str(self.goal),
            "latex_goal": latex.convert_expr(self.goal),
            "induct_var": self.induct_var,
            "base_case": self.base_case.export(),
            "induct_case": self.induct_case.export(),
            "finished": self.is_finished()
        }

    def get_by_label(self, label: Label):
        if label.empty():
            return self
        elif label.head == 0:
            return self.base_case.get_by_label(label.tail)
        elif label.head == 1:
            return self.induct_case.get_by_label(label.tail)
        else:
            raise AssertionError("get_by_label: invalid label")


class CompState:
    """Represents the global state of a computation proof."""
    def __init__(self, name: str, goal: Expr):
        # Name of the proof
        self.name = name

        # Final goal of the computation
        self.goal = goal

        # List of items in the computation
        self.items = []

        # Dictionary mapping function names to their definitions
        self.func_map = dict()

    def __str__(self):
        res = "Goal: %s\n" % self.goal
        for item in self.items:
            res += str(item)
        return res

    def export(self):
        return {
            "name": self.name,
            "type": "CompState",
            "problem": str(self.goal),
            "latex_problem": latex.convert_expr(self.goal),
            "items": [item.export() for item in self.items]
        }

    def add_item(self, item: StateItem):
        """Add an item of computation."""
        self.items.append(item)
        if isinstance(item, FuncDef):
            self.func_map[item.symb] = item

    def get_by_label(self, label: Union[str, Label]):
        """Return an item corresponding to a label"""
        if isinstance(label, str):
            label = Label(label)
        if label.empty():
            return self
        else:
            return self.items[label.head].get_by_label(label.tail)

    def next_step_label(self, label: Label) -> Label:
        step = self.get_by_label(label)
        if isinstance(step, Calculation):
            return Label(label.data + [0])
        elif isinstance(step, CalculationStep):
            return Label(label.data[:-1] + [label.data[-1] + 1])
        else:
            raise NotImplementedError


class CompFile:
    """Represent a file containing multiple CompState objects."""
    def __init__(self, name: str):
        self.name = name
        self.content = []

    def __str__(self):
        res = "File %s\n" % self.name
        for st in self.content:
            res += str(st)
        return res

    def add_definition(self, funcdef: FuncDef):
        """Add a function definition."""
        self.content.append(funcdef)

    def add_compstate(self, st: CompState):
        """Add a computation proof."""
        self.content.append(st)

    def add_calculation(self, calc: Union[str, Expr, Calculation]) -> Calculation:
        """Add a calculation."""
        if isinstance(calc, str):
            self.content.append(Calculation(parser.parse_expr(calc)))
        elif isinstance(calc, Expr):
            self.content.append(Calculation(calc))
        elif isinstance(calc, Calculation):
            self.content.append(calc)
        else:
            raise NotImplementedError
        return self.content[-1]

    def add_goal(self, goal: Goal):
        """Add a goal."""
        self.content.append(goal)

    def export(self):
        return {
            "name": self.name,
            "content": [item.export() for item in self.content]
        }


def parse_rule(item) -> Rule:
    if 'loc' in item:
        if item['loc'] == 'subterms':
            del item['loc']
            return rules.OnSubterm(parse_rule(item))
        else:
            loc = item['loc']
            del item['loc']
            return rules.OnLocation(parse_rule(item), loc)
    elif item['name'] == 'ExpandDefinition':
        func_def = parser.parse_expr(item['func_def'])
        return rules.ExpandDefinition(func_def)
    elif item['name'] == 'DerivIntExchange':
        return rules.DerivIntExchange()
    elif item['name'] == 'FullSimplify':
        return rules.FullSimplify()
    elif item['name'] == 'ElimInfInterval':
        a = Const(0)
        if 'a' in item:
            a = parser.parse_expr(item['a'])
        return rules.ElimInfInterval(a)
    elif item['name'] == 'SubstitutionInverse':
        var_name = item['var_name']
        var_subst = parser.parse_expr(item['var_subst'])
        return rules.SubstitutionInverse(var_name, var_subst)
    else:
        raise NotImplementedError

def parse_step(item, parent: Calculation, id: int) -> CalculationStep:
    if item['type'] != 'CalculationStep':
        raise AssertionError('parse_step')

    rule = parse_rule(item['rule'])
    res = parser.parse_expr(item['res'])
    step = CalculationStep(rule, res, parent, id)
    return step

def parse_conds(item) -> Conditions:
    res = Conditions()
    if 'conds' in item:
        for subitem in item['conds']:
            if subitem['type'] != 'Condition':
                raise AssertionError('parse_conds')        
            res.add_condition(subitem['name'], parser.parse_expr(subitem['cond']))
    return res

def parse_item(item) -> StateItem:
    if item['type'] == 'FuncDef':
        conds = parse_conds(item)
        eq = parser.parse_expr(item['eq'])
        return FuncDef(eq, conds=conds)
    elif item['type'] == 'Goal':
        goal = parser.parse_expr(item['goal'])
        conds = parse_conds(item)
        res = Goal(goal, conds=conds)
        if 'proof' in item:
            res.proof = parse_item(item['proof'])
        return res
    elif item['type'] == 'CalculationProof':
        goal = parser.parse_expr(item['goal'])
        res = CalculationProof(goal)
        res.lhs_calc = parse_item(item['lhs_calc'])
        res.rhs_calc = parse_item(item['rhs_calc'])
        return res
    elif item['type'] == 'Calculation':
        start = parser.parse_expr(item['start'])
        res = Calculation(start)
        for i, step in enumerate(item['steps']):
            res.add_step(parse_step(step, res, i))
        return res
    elif item['type'] == 'InductionProof':
        goal = parser.parse_expr(item['goal'])
        induct_var = item['induct_var']
        res = InductionProof(goal, induct_var)
        res.base_case = parse_item(item['base_case'])
        res.induct_case = parse_item(item['induct_case'])
        return res
    else:
        raise NotImplementedError

def parse_state(name: str, problem: str, items) -> CompState:
    goal = parser.parse_expr(problem)
    st = CompState(name, goal)
    for item in items:
        st.add_item(parse_item(item))
    return st
