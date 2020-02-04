"""Abstraction for parsing and processing of different types of items."""

import traceback2
import itertools

from kernel.type import TVar, TConst, TFun, BoolType
from kernel import term
from kernel.term import Term, Var, Const, And, Implies, Not, Eq, Forall
from kernel.thm import Thm
from kernel import theory
from kernel import extension
from logic import context
from syntax import parser
from syntax import printer
from syntax import pprint
from syntax.settings import settings, global_setting


class ItemException(Exception):
    """Exception when checking an item."""
    def __init__(self, err):
        self.err = err

    def __str__(self):
        return self.err


class Item:
    """Base class for different types of items."""
    def __init__(self, data):
        self.error = None

    def parse(self, data):
        """Parse an item from data in JSON format."""
        raise NotImplementedError

    def get_extension(self):
        """Obtain the extension corresponding to the item.

        Call only when self.error is None.

        """
        raise NotImplementedError

    def get_display(self):
        """Obtain data for display or edit.
        
        Normally, use highlight=False, unicode=True for edit, and
        highlight=True, unicode=True for display.

        """
        raise NotImplementedError

    def parse_edit(self, edit_data):
        """Parse the given edit_data to the object."""
        raise NotImplementedError

    def export_json(self):
        """Export the object to JSON format."""
        raise NotImplementedError

    def export_web(self):
        res = self.export_json()
        with global_setting(highlight=True, unicode=True):
            res['display'] = self.get_display()
        with global_setting(highlight=False, unicode=True):
            res['edit'] = self.get_display()
        if self.error is None:
            with global_setting(highlight=False, unicode=True, line_length=None):
                res['ext'] = printer.print_extensions(self.get_extension())
        else:
            res['error'] = {
                "err_type": self.error.__class__.__name__,
                "err_str": str(self.error),
                "trace": self.trace
            }
        return res


def export_term(t):
    """Function for printing a term for export to json."""
    with global_setting(unicode=True, line_length=80):
        res = printer.print_term(t)
    if len(res) == 1:
        res = res[0]
    return res

def display_raw(s):
    """Display unparsed type or term."""
    if isinstance(s, str):
        return [pprint.N(s)]
    else:
        return [pprint.N(line) for line in s]

def display_term(t):
    """Display parsed term."""
    res = printer.print_term(t)
    if not settings.highlight and settings.line_length is not None:
        return '\n'.join(res)
    else:
        return res


class Constant(Item):
    """Axiomatic constant."""
    def __init__(self):
        self.ty = 'def.ax'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.overloaded = False  # whether the constant is overloadable
        self.cname = None  # expanded name of the constant (for linking)
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.overloaded == other.overloaded and self.cname == other.cname and self.error == other.error

    def parse(self, data):
        self.name = data['name']
        if 'overloaded' in data and data['overloaded']:
            self.overloaded = True

        try:
            self.type = parser.parse_type(data['type'])
            if self.overloaded:
                self.cname = self.name
            else:
                self.cname = theory.thy.get_overload_const_name(self.name, self.type)
        except Exception as error:
            self.type = data['type']
            self.error = error
            self.trace = traceback2.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))
        if self.overloaded:
            res.append(extension.Overload(self.name))
        return res

    def get_display(self):
        return {
            'ty': 'def.ax',
            'name': self.name,
            'type': display_raw(self.type) if self.error else printer.print_type(self.type),
            'overloaded': self.overloaded
        }

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            res = {
                'ty': 'def.ax',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type)
            }
        if self.overloaded:
            res['overloaded'] = True
        return res

class Axiom(Item):
    """Axiom."""
    def __init__(self):
        self.ty = 'thm.ax'
        self.name = None  # name of the axiom
        self.vars = dict()  # variable declarations
        self.prop = None  # proposition
        self.attributes = list()  # list of attributes
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.vars == other.vars and \
            self.prop == other.prop and self.attributes == other.attributes and self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            with context.fresh_context(vars=data['vars']):
                self.vars = context.ctxt.vars
                self.prop = parser.parse_term(data['prop'])

            # theorem does not already exist
            if theory.thy.has_theorem(self.name):
                raise ItemException("Theorem %s: theorem already exists")

            # prop should not contain extra variables
            self_vars = set(self.vars.keys())
            prop_vars = set(v.name for v in term.get_vars(self.prop))
            if not prop_vars.issubset(self_vars):
                raise ItemException(
                    "Theorem %s: extra variables in prop: %s" % (
                        self.name, ", ".join(v for v in prop_vars - self_vars)))

        except Exception as error:
            self.vars = data['vars']
            self.prop = data['prop']
            self.error = error
            self.trace = traceback2.format_exc()
        
        if 'attributes' in data:
            self.attributes = data['attributes']
        
    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Theorem(self.name, Thm([], self.prop)))
        for attr in self.attributes:
            res.append(extension.Attribute(self.name, attr))
        return res

    def get_display(self):
        if self.error:
            disp_vars = [pprint.N(nm + ' :: ' + T) for nm, T in self.vars.items()]
            disp_prop = display_raw(self.prop)
        else:
            disp_vars = [pprint.N(nm + ' :: ') + printer.print_type(T) for nm, T in self.vars.items()]
            disp_prop = display_term(self.prop)

        return {
            'ty': 'thm.ax',
            'name': self.name,
            'vars': disp_vars if settings.highlight else '\n'.join(disp_vars),
            'prop': disp_prop,
            'attributes': self.attributes
        }

    def parse_edit(self, edit_data):
        vars = dict()
        for var_decl in edit_data['vars'].split('\n'):
            if var_decl.strip():
                nm, T = [s.strip() for s in var_decl.split('::')]
                vars[nm] = T
        edit_data['vars'] = vars
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            res = {
                'ty': 'thm.ax',
                'name': self.name,
                'vars': self.vars if self.error else \
                    dict((nm, printer.print_type(T)) for nm, T in self.vars.items()),
                'prop': self.prop if self.error else export_term(self.prop)
            }
        if self.attributes:
            res['attributes'] = self.attributes
        return res

class Theorem(Axiom):
    """Theorem"""
    def __init__(self):
        super().__init__()
        self.ty = 'thm'
        self.steps = None
        self.proof = None
        self.num_gaps = None

    def __eq__(self, other):
        return super().__eq__(other) and self.steps == other.steps and self.proof == other.proof and \
            self.num_gaps == other.num_gaps

    def parse(self, data):
        super().parse(data)

        # Just store the proof information without processing them
        if 'steps' in data:
            self.steps = data['steps']
        if 'proof' in data:
            self.proof = data['proof']
        if 'num_gaps' in data:
            self.num_gaps = data['num_gaps']

    def get_extension(self):
        return super().get_extension()

    def get_display(self):
        res = super().get_display()
        res['ty'] = 'thm'
        return res

    def get_proof(self):
        res = dict()
        if self.steps:
            res['steps'] = self.steps
        if self.proof:
            res['proof'] = self.proof
        if self.num_gaps is not None:
            res['num_gaps'] = self.num_gaps
        return res

    def parse_edit(self, edit_data):
        super().parse_edit(edit_data)

    def export_json(self):
        res = super().export_json()
        res['ty'] = 'thm'
        if self.steps:
            res['steps'] = self.steps
        if self.proof:
            res['proof'] = self.proof
        if self.num_gaps is not None:
            res['num_gaps'] = self.num_gaps
        return res

class Definition(Item):
    """Definition"""
    def __init__(self):
        self.ty = 'def'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.prop = None  # defining proposition
        self.cname = None  # expanded name of the constant (for linking)
        self.attributes = []
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.prop == other.prop and self.cname == other.cname and self.attributes == other.attributes and \
            self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            self.type = parser.parse_type(data['type'])
            self.cname = theory.thy.get_overload_const_name(self.name, self.type)

            with context.fresh_context(defs={self.name: self.type}):
                self.prop = parser.parse_term(data['prop'])

            # prop should be an equality
            if not self.prop.is_equals():
                raise ItemException("Definition %s: prop is not an equality" % self.name)
            
            f, args = self.prop.lhs.strip_comb()
            if f != Const(self.name, self.type):
                raise ItemException("Definition %s: wrong head of lhs" % self.name)
            lhs_vars = set(v.name for v in args)
            rhs_vars = set(v.name for v in term.get_vars(self.prop.rhs))
            if len(lhs_vars) != len(args):
                raise ItemException("Definition %s: variables on lhs must be distinct" % self.name)
            if not rhs_vars.issubset(lhs_vars):
                raise ItemException(
                    "Definition %s: extra variables in rhs: %s" % (
                        self.name, ", ".join(v for v in rhs_vars - lhs_vars)))

        except Exception as error:
            self.type = data['type']
            self.prop = data['prop']
            self.error = error
            self.trace = traceback2.format_exc()

        if 'attributes' in data:
            self.attributes = data['attributes']

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))
        res.append(extension.Theorem(self.cname + "_def", Thm([], self.prop)))
        for attr in self.attributes:
            res.append(extension.Attribute(self.cname + "_def", attr))
        return res

    def get_display(self):
        if self.error:
            disp_type = display_raw(self.type)
            disp_prop = display_raw(self.prop)
        else:
            disp_type = printer.print_type(self.type)
            disp_prop = display_term(self.prop)
        
        return {
            'ty': 'def',
            'name': self.name,
            'type': disp_type,
            'prop': disp_prop,
            'attributes': self.attributes
        }
    
    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            res = {
                'ty': 'def',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type),
                'prop': self.prop if self.error else export_term(self.prop)
            }
        if self.attributes:
            res['attributes'] = self.attributes
        return res

class Fun(Item):
    """Inductively defined functions.
    
    An inductively defined function is specified by its name, type, and
    a list of equations. Each equation specifies a rewriting rule for the
    defined constant. The rules may be recursive, but must be clearly
    terminating.

    For example, addition on natural numbers is specified by:
    fun plus :: nat => nat => nat
      plus 0 n = n
      plus (Suc m) n = Suc (plus m n)

    and multiplication on natural numbers is specified by:
    fun times :: nat => nat => nat
      times 0 n = 0
      times (Suc m) n = plus n (times m n)

    """
    def __init__(self):
        self.ty = 'def.ind'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.rules = []  # list of equality rules
        self.cname = None  # expanded name of the constant (for linking)
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.rules == other.rules and self.cname == other.cname and self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            self.type = parser.parse_type(data['type'])
            self.cname = theory.thy.get_overload_const_name(self.name, self.type)

            for rule in data['rules']:
                with context.fresh_context(defs={self.name: self.type}):
                    prop = parser.parse_term(rule['prop'])

                # prop should be an equality
                if not prop.is_equals():
                    raise ItemException("Fun %s: rule is not an equality" % self.name)

                f, args = prop.lhs.strip_comb()
                if f != Const(self.name, self.type):
                    raise ItemException("Fun %s: wrong head of lhs" % self.name)
                lhs_vars = set(v.name for v in term.get_vars(prop.lhs))
                rhs_vars = set(v.name for v in term.get_vars(prop.rhs))
                if not rhs_vars.issubset(lhs_vars):
                    raise ItemException(
                        "Fun %s: extra variables in rhs: %s" % (
                            self.name, ", ".join(v for v in rhs_vars - lhs_vars)))

                self.rules.append({'prop': prop})
            
        except Exception as error:
            self.type = data['type']
            self.rules = data['rules']
            self.error = error
            self.trace = traceback2.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))
        for i, rule in enumerate(self.rules):
            th_name = self.cname + "_def_" + str(i + 1)
            res.append(extension.Theorem(th_name, Thm([], rule['prop'])))
            res.append(extension.Attribute(th_name, "hint_rewrite"))
        return res

    def get_display(self):
        if self.error:
            disp_type = display_raw(self.type)
            disp_rules = [rule['prop'] for rule in self.rules]
        else:
            disp_type = printer.print_type(self.type)
            with global_setting(line_length=None):
                disp_rules = [printer.print_term(rule['prop']) for rule in self.rules]
        
        return {
            'ty': 'def.ind',
            'name': self.name,
            'type': disp_type,
            'rules': disp_rules if settings.highlight else '\n'.join(disp_rules)
        }

    def parse_edit(self, edit_data):
        rules = []
        for prop in edit_data['rules'].split('\n'):
            rules.append({'prop': prop})
        edit_data['rules'] = rules
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            return {
                'ty': 'def.ind',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type),
                'rules': [{'prop': rule['prop'] if self.error else export_term(rule['prop'])}
                          for rule in self.rules]
            }

class Inductive(Item):
    """Inductively defined predicate.

    An inductive predicate is specified by its name and type, and a list
    of introduction rules. We require each introduction rule be named.
    The conclusion of each introduction rule must correspond to the defined
    constant.

    """
    def __init__(self):
        self.ty = 'def.pred'
        self.name = None  # name of the constant
        self.type = None  # type of the constant
        self.rules = []  # list of introduction rules
        self.cname = None  # expected name of the constant (for linking)
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.type == other.type and \
            self.rules == other.rules and self.cname == other.cname and self.error == other.error

    def parse(self, data):
        self.name = data['name']

        try:
            self.type = parser.parse_type(data['type'])
            self.cname = theory.thy.get_overload_const_name(self.name, self.type)

            for rule in data['rules']:
                with context.fresh_context(defs={self.name: self.type}):
                    prop = parser.parse_term(rule['prop'])

                # Test conclusion of the prop
                _, concl = prop.strip_implies()
                f, _ = concl.strip_comb()
                if f != Const(self.name, self.type):
                    raise ItemException("Inductive %s: wrong head of conclusion" % self.name)

                self.rules.append({'name': rule['name'], 'prop': prop})

        except Exception as error:
            self.type = data['type']
            self.rules = data['rules']
            self.error = error
            self.trace = traceback2.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.Constant(self.name, self.type, ref_name=self.cname))

        for rule in self.rules:
            res.append(extension.Theorem(rule['name'], Thm([], rule['prop'])))
            res.append(extension.Attribute(rule['name'], 'hint_backward'))

        # Case rule
        Targs, _ = self.type.strip_type()
        vars = []
        for i, Targ in enumerate(Targs):
            vars.append(Var("_a" + str(i+1), Targ))

        P = Var("P", BoolType)
        pred = Const(self.name, self.type)
        assum0 = pred(*vars)
        assums = []
        for rule in self.rules:
            prop = rule['prop']
            As, C = prop.strip_implies()
            eq_assums = [Eq(var, arg) for var, arg in zip(vars, C.args)]
            assum = Implies(*(eq_assums + As), P)
            prop_vars = term.get_vars(prop)
            for var in reversed(term.get_vars(prop)):
                assum = Forall(var, assum)
            assums.append(assum)

        prop = Implies(*([assum0] + assums + [P]))
        res.append(extension.Theorem(self.cname + "_cases", Thm([], prop)))

        return res

    def get_display(self):
        if self.error:
            disp_type = display_raw(self.type)
            disp_rules = [pprint.N(rule['name'] + ": " + rule['prop']) for rule in self.rules]
        else:
            disp_type = printer.print_type(self.type)
            with global_setting(line_length=None):
                disp_rules = [pprint.N(rule['name'] + ": ") + printer.print_term(rule['prop'])
                            for rule in self.rules]
        
        return {
            'ty': 'def.pred',
            'name': self.name,
            'type': disp_type,
            'rules': disp_rules if settings.highlight else '\n'.join(disp_rules)
        }

    def parse_edit(self, edit_data):
        rules = []
        for rule in edit_data['rules'].split('\n'):
            name, prop = [s.strip() for s in rule.split(':', 1)]
            rules.append({'name': name, 'prop': prop})
        edit_data['rules'] = rules
        self.parse(edit_data)

    def export_json(self):
        with global_setting(unicode=True):
            return {
                'ty': 'def.pred',
                'name': self.name,
                'type': self.type if self.error else printer.print_type(self.type),
                'rules': [{'name': rule['name'],
                           'prop': rule['prop'] if self.error else export_term(rule['prop'])}
                          for rule in self.rules]
            }

class AxType(Item):
    """Axiomatic types."""
    def __init__(self):
        self.ty = 'type.ax'
        self.name = None  # name of the type
        self.args = list()  # list of type arguments
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.args == other.args and \
            self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.args = data['args']

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []
        res.append(extension.TConst(self.name, len(self.args)))
        return res

    def get_display(self):
        Targs = [TVar(arg) for arg in self.args]
        T = TConst(self.name, *Targs)
        return {
            'ty': 'type.ax',
            'type': printer.print_type(T)
        }

    def parse_edit(self, edit_data):
        T = parser.parse_type(edit_data['type'], check_type=False)
        data = {
            'ty': 'type.ax',
            'name': T.name,
            'args': [argT.name for argT in T.args]
        }
        self.parse(data)

    def export_json(self):
        return {
            'ty': 'type.ax',
            'name': self.name,
            'args': self.args
        }

class Datatype(Item):
    """Inductive datatypes.
    
    An inductive datatype is specified by its name, its arity (as a list
    of default names of type arguments), and a list of constructors.

    For example, the natural numbers is defined by:
    datatype nat =
      zero
      Suc (n :: nat)

    and the type of lists is defined by:
    datatype 'a list =
      nil
      cons (x :: 'a) (xs :: 'a list)
    
    """
    def __init__(self):
        self.ty = 'type.ind'
        self.name = None  # name of the type
        self.args = list()  # list of type arguments
        self.constrs = list()  # list of type constructors
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.name == other.name and self.args == other.args and \
            self.constrs == other.constrs and self.error == other.error

    def parse(self, data):
        self.name = data['name']
        self.args = data['args']
        theory.thy.add_type_sig(self.name, len(self.args))

        try:
            for constr in data['constrs']:
                constr_type = parser.parse_type(constr['type'])
                self.constrs.append({
                    'name': constr['name'],
                    'type': constr_type,
                    'cname': theory.thy.get_overload_const_name(constr['name'], constr_type),
                    'args': constr['args']
                })
        except Exception as error:
            self.constrs = data['constrs']
            self.error = error
            self.trace = traceback2.format_exc()

    def get_extension(self):
        assert self.error is None, "get_extension"
        res = []

        # Add to type and term signature.
        res.append(extension.TConst(self.name, len(self.args)))
        for constr in self.constrs:
            res.append(extension.Constant(constr['name'], constr['type'], ref_name=constr['cname']))

        # Add non-equality theorems.
        for constr1, constr2 in itertools.combinations(self.constrs, 2):
            # For each A x_1 ... x_m and B y_1 ... y_n, get the theorem
            # ~ A x_1 ... x_m = B y_1 ... y_n.
            argT1, _ = constr1['type'].strip_type()
            argT2, _ = constr2['type'].strip_type()
            lhs_vars = [Var(nm, T) for nm, T in zip(constr1['args'], argT1)]
            rhs_vars = [Var(nm, T) for nm, T in zip(constr2['args'], argT2)]
            A = Const(constr1['name'], constr1['type'])
            B = Const(constr2['name'], constr2['type'])
            lhs = A(*lhs_vars)
            rhs = B(*rhs_vars)
            neq = Not(Eq(lhs, rhs))
            th_name = "%s_%s_%s_neq" % (self.name, constr1['name'], constr2['name'])
            res.append(extension.Theorem(th_name, Thm([], neq)))

        # Add injectivity theorems.
        for constr in self.constrs:
            # For each A x_1 ... x_m with m > 0, get the theorem
            # A x_1 ... x_m = A x_1' ... x_m' --> x_1 = x_1' & ... & x_m = x_m'
            if constr['args']:
                argT, _ = constr['type'].strip_type()
                lhs_vars = [Var(nm, T) for nm, T in zip(constr['args'], argT)]
                rhs_vars = [Var(nm + "1", T) for nm, T in zip(constr['args'], argT)]
                A = Const(constr['name'], constr['type'])
                assum = Eq(A(*lhs_vars), A(*rhs_vars))
                concls = [Eq(var1, var2) for var1, var2 in zip(lhs_vars, rhs_vars)]
                concl = And(*concls)
                th_name = "%s_%s_inject" % (self.name, constr['name'])
                res.append(extension.Theorem(th_name, Thm([], Implies(assum, concl))))

        # Add the inductive theorem.
        tvars = [TVar(targ) for targ in self.args]
        T = TConst(self.name, *tvars)
        var_P = Var("P", TFun(T, BoolType))
        ind_assums = []
        for constr in self.constrs:
            A = Const(constr['name'], constr['type'])
            argT, _ = constr['type'].strip_type()
            args = [Var(nm, T2) for nm, T2 in zip(constr['args'], argT)]
            C = var_P(A(*args))
            As = [var_P(Var(nm, T2)) for nm, T2 in zip(constr['args'], argT) if T2 == T]
            ind_assum = Implies(*(As + [C]))
            for arg in reversed(args):
                ind_assum = Forall(arg, ind_assum)
            ind_assums.append(ind_assum)
        ind_concl = var_P(Var("x", T))
        th_name = self.name + "_induct"
        res.append(extension.Theorem(th_name, Thm([], Implies(*(ind_assums + [ind_concl])))))
        res.append(extension.Attribute(th_name, "var_induct"))

        return res

    def get_display(self):
        Targs = [TVar(arg) for arg in self.args]
        T = TConst(self.name, *Targs)
        constrs = []
        for constr in self.constrs:
            argsT, _ = constr['type'].strip_type()
            res = pprint.N(constr['name'])
            for i, arg in enumerate(constr['args']):
                res += pprint.N(' (' + arg + ' :: ') + printer.print_type(argsT[i]) + pprint.N(')')
            constrs.append(res)

        return {
            'ty': 'type.ind',
            'type': printer.print_type(T),
            'constrs': constrs if settings.highlight else '\n'.join(constrs)
        }

    def parse_edit(self, edit_data):
        T = parser.parse_type(edit_data['type'])
        constrs = []
        for constr_decl in edit_data['constrs'].split('\n'):
            constr = parser.parse_ind_constr(constr_decl)
            constr['type'] = str(TFun(*(constr['type'] + [T])))
            constrs.append(constr)

        data = {
            'ty': 'type.ind',
            'name': T.name,
            'args': [argT.name for argT in T.args],
            'constrs': constrs
        }

        self.parse(data)

    def export_json(self):
        constrs = []
        for constr in self.constrs:
            constrs.append({
                'name': constr['name'],
                'args': constr['args'],
                'type': constr['type'] if self.error else printer.print_type(constr['type'])
            })
        return {
            'ty': 'type.ind',
            'name': self.name,
            'args': self.args,
            'constrs': constrs
        }

class Header(Item):
    """Header"""
    def __init__(self):
        self.ty = 'header'
        self.depth = None
        self.name = None
        self.error = None

    def __eq__(self, other):
        return self.ty == other.ty and self.depth == other.depth and self.name == other.name and \
            self.error == other.error

    def parse(self, data):
        self.depth = data['depth']
        self.name = data['name']

    def get_extension(self):
        return []

    def get_display(self):
        return {
            'ty': 'header',
            'depth': self.depth,
            'name': self.name
        }

    def parse_edit(self, edit_data):
        self.parse(edit_data)

    def export_json(self):
        return {
            'ty': 'header',
            'depth': self.depth,
            'name': self.name
        }


item_table = {
    'def.ax': Constant,
    'thm.ax': Axiom,
    'thm': Theorem,
    'def': Definition,
    'def.ind': Fun,
    'def.pred': Inductive,
    'type.ax': AxType,
    'type.ind': Datatype,
    'header': Header
}

def parse_item(data):
    obj = item_table[data['ty']]()
    obj.parse(data)
    return obj

def parse_edit(edit_data):
    obj = item_table[edit_data['ty']]()
    obj.parse_edit(edit_data)
    return obj
