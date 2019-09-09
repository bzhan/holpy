# Author: Bohua Zhan

from kernel.type import TFun
from kernel import term
from data.int import intT
from data import int as hol_int
from data.list import listT, nth, length
from logic import logic


"""Expressions in the programming language."""

class Expr():
    """Base class for expressions."""
    def __init__(self):
        # Whether the expression is an identifier.
        self.is_ident = None

    def convert_hol(self, ctxt):
        """Conversion to a HOL term."""
        raise NotImplementedError

    def subst(self, inst):
        """Substitute using an instantiation."""
        raise NotImplementedError

class Var(Expr):
    """Variables."""
    def __init__(self, name):
        assert isinstance(name, str)
        self.name = name
        self.is_ident = True

    def __repr__(self):
        return "Var(%s)" % self.name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def convert_hol(self, ctxt):
        assert self.name in ctxt
        if ctxt[self.name] == "int":
            return term.Var(self.name, intT)
        elif ctxt[self.name] == "int array":
            return term.Var(self.name, listT(intT))
        else:
            raise NotImplementedError

    def subst(self, inst):
        if self.name in inst:
            return inst[self.name]
        else:
            return self

class ArrayElt(Expr):
    """Element of an array."""
    def __init__(self, ident, idx):
        assert isinstance(ident, Expr) and ident.is_ident and isinstance(idx, Expr)
        self.ident = ident
        self.idx = idx
        self.is_ident = True

    def __repr__(self):
        return "ArrayElt(%s,%s)" % (repr(self.ident), repr(self.idx))

    def __str__(self):
        return "%s[%s]" % (str(self.ident), str(self.idx))

    def __eq__(self, other):
        return isinstance(other, ArrayElt) and self.ident == other.ident and self.idx == other.idx

    def convert_hol(self, ctxt):
        return list.nth(convert_hol(self.ident, ctxt), convert_hol(self.idx, ctxt))

    def subst(self, inst):
        return self

class Field(Expr):
    """Field of an identifier. This includes length of an array
    (given by 'length').
    
    """
    def __init__(self, ident, fieldname):
        assert isinstance(ident, Expr) and ident.is_ident and isinstance(fieldname, str)
        self.ident = ident
        self.fieldname = fieldname
        self.is_ident = True

    def __repr__(self):
        return "Field(%s,%s)" % (repr(self.ident), self.fieldname)

    def __str__(self):
        return "%s.%s" % (str(self.ident), self.fieldname)

    def __eq__(self, other):
        return isinstance(other, Field) and self.ident == other.ident and self.fieldname == other.fieldname

    def convert_hol(self, ctxt):
        if self.fieldname == "length":
            return list.length(convert_hol(self.ident, ctxt))
        else:
            raise NotImplementedError

    def subst(self, inst):
        return self

class Const(Expr):
    """Constant value."""
    def __init__(self, val):
        assert isinstance(val, (int, bool))
        self.val = val

    def __repr__(self):
        return "Const(%s)" % str(self.val)

    def __str__(self):
        if isinstance(self.val, bool):
            return "true" if self.val else "false"
        else:
            return str(self.val)

    def __eq__(self, other):
        return isinstance(other, Const) and type(self.val) == type(other.val) and self.val == other.val

    def convert_hol(self, ctxt):
        if type(self.val) == int:
            return hol_int.to_binary_int(self.val)
        elif type(self.val) == bool:
            return logic.true if self.val else logic.false
        else:
            raise NotImplementedError

    def subst(self, inst):
        return self

class Op(Expr):
    """One of pre-specified operators."""
    def __init__(self, op, *args):
        assert isinstance(op, str)
        assert all(isinstance(arg, Expr) for arg in args)
        self.op = op

        if len(args) == 1:
            assert op in ["-", "~"]
        else:
            assert len(args) == 2
            assert op in [
                "+", "-", "*",  # arithmetic
                "==", "!=", "<=", "<", ">=", ">",  # comparison
                "&", "|", "-->", "<-->",  # boolean
            ]

        self.args = list(args)

    def __repr__(self):
        return "Op(%s,%s)" % (self.op, ",".join(repr(arg) for arg in self.args))

    def __str__(self):
        if len(self.args) == 1:
            return "%s%s" % (self.op, str(self.args[0]))
        elif len(self.args) == 2:
            return "%s %s %s" % (str(self.args[0]), self.op, str(self.args[1]))
        else:
            raise NotImplementedError

    def __eq__(self, other):
        return isinstance(other, Op) and self.op == other.op and self.args == other.args

    def convert_hol(self, ctxt):
        if len(self.args) == 1:
            e = self.args[0].convert_hol(ctxt)
            if self.op == "-":
                return hol_int.uminus(e)
            elif self.op == "~":
                return logic.neg(e)
            else:
                raise NotImplementedError
        elif len(self.args) == 2:
            e1, e2 = self.args[0].convert_hol(ctxt), self.args[1].convert_hol(ctxt)
            if self.op == "+":
                return hol_int.plus(e1, e2)
            elif self.op == "-":
                return hol_int.minus(e1, e2)
            elif self.op == "*":
                return hol_int.times(e1, e2)
            elif self.op == "==":
                return term.Term.mk_equals(e1, e2)
            elif self.op == "!=":
                return logic.neg(term.Term.mk_equals(e1, e2))
            elif self.op == "<=":
                return hol_int.less_eq(e1, e2)
            elif self.op == "<":
                return hol_int.less(e1, e2)
            elif self.op == ">=":
                return hol_int.less_eq(e2, e1)
            elif self.op == ">":
                return hol_int.less(e2, e1)
            elif self.op == "&":
                return logic.conj(e1, e2)
            elif self.op == "|":
                return logic.disj(e1, e2)
            elif self.op == "-->":
                return term.Term.mk_implies(e1, e2)
            elif self.op == "<-->":
                return term.Term.mk_equals(e1, e2)
            else:
                raise NotImplementedError
        else:
            raise NotImplementedError

    def subst(self, inst):
        return Op(self.op, *(arg.subst(inst) for arg in self.args))

class Fun(Expr):
    """Function application."""
    def __init__(self, fname, *args):
        assert isinstance(fname, str)
        assert all(isinstance(arg, Expr) for arg in args)
        self.fname = fname
        self.args = list(args)

    def __repr__(self):
        return "Fun(%s,%s)" % (self.fname, ",".join(repr(arg) for arg in self.args))

    def __str__(self):
        return "%s(%s)" % (self.fname, ",".join(str(arg) for arg in self.args))

    def __eq__(self, other):
        return isinstance(other, Fun) and self.fname == other.fname and self.args == other.args

    def convert_hol(self, ctxt):
        assert self.fname in global_fnames
        name, T = global_fnames[self.fname]
        hol_args = [arg.convert_hol(ctxt) for arg in self.args]
        return term.Const(name, T)(*hol_args)

    def subst(self, inst):
        return Fun(self.fname, *(arg.subst(inst) for arg in self.args))

class ITE(Expr):
    """If-then-else expressions."""
    def __init__(self, cond, e1, e2):
        assert isinstance(cond, Expr) and isinstance(e1, Expr) and isinstance(e2, Expr)
        self.cond = cond
        self.e1 = e1
        self.e2 = e2

    def __repr__(self):
        return "ITE(%s,%s,%s)" % (repr(self.cond), repr(self.e1), repr(self.e2))

    def __str__(self):
        return "if %s then %s else %s" % (str(self.cond), str(self.e1), str(self.e2))

    def __eq__(self, other):
        return isinstance(other, ITE) and self.cond == other.cond and \
            self.e1 == other.e1 and self.e2 == other.e2

    def convert_hol(self, ctxt):
        P, x, y = [a.convert_hol(ctxt) for a in [self.cond, self.e1, self.e2]]
        return logic.mk_if(P, x, y)

    def subst(self, inst):
        return ITE(self.cond.subst(inst), self.e1.subst(inst), self.e2.subst(inst))

class Forall(Expr):
    """Forall expressions."""
    def __init__(self, var, e):
        assert isinstance(var, Var) and isinstance(e, Expr)
        self.var = var
        self.e = e

    def __repr__(self):
        return "Forall(%s,%s)" % (repr(self.var), repr(self.e))

    def __str__(self):
        return "forall %s. %s" % (str(self.var), str(self.e))

    def __eq__(self, other):
        return isinstance(other, Forall) and self.var == other.var and self.e == other.e

    def convert_hol(self, ctxt):
        raise NotImplementedError

    def subst(self, inst):
        if self.var.name in inst:
            raise NotImplementedError

        return Forall(self.var, self.e.subst(inst))


def implies(e1, e2):
    return Op("-->", e1, e2)

def conj(e1, e2):
    return Op("&", e1, e2)

def neg(e):
    return Op("~", e)

def plus(e1, e2):
    return Op("+", e1, e2)

def minus(e1, e2):
    return Op("-", e1, e2)

def uminus(e):
    return Op("-", e)

def times(e1, e2):
    return Op("*", e1, e2)

def less(e1, e2):
    return Op("<", e1, e2)

def less_eq(e1, e2):
    return Op("<=", e1, e2)

def eq(e1, e2):
    return Op("==", e1, e2)

def neq(e1, e2):
    return Op("!=", e1, e2)

true = Const(True)
zero = Const(0)
one = Const(1)

global_fnames = {
    "abs": ("int_abs", TFun(intT, intT)),
    "max": ("int_max", TFun(intT, intT, intT)),
}