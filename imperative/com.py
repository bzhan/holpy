# Author: Bohua Zhan

"""Basic data structure for programs."""

from kernel.term import Term
from logic import logic
from data import int

def print_term(t):
    """A simple function for printing terms in the imp format."""
    def rec(t):
        if t.is_equals():
            return rec(t.arg1) + " == " + rec(t.arg)
        elif logic.is_neg(t) and t.arg.is_equals():
            return rec(t.arg.arg1) + " != " + rec(t.arg.arg)
        elif Term.is_implies(t):
            return rec(t.arg1) + " --> " + rec(t.arg)
        elif logic.is_conj(t):
            return rec(t.arg1) + " & " + rec(t.arg)
        elif logic.is_disj(t):
            return rec(t.arg1) + " | " + rec(t.arg)
        elif logic.is_neg(t):
            return "~" + rec(t.arg)
        elif logic.is_if(t):
            b, b1, b2 = t.args
            return "if " + rec(b) + " then " + rec(b1) + " else " + rec(b2)
        elif int.is_less_eq(t):
            return rec(t.arg1) + " <= " + rec(t.arg)
        elif int.is_less(t):
            return rec(t.arg1) + " < " + rec(t.arg)
        elif int.is_plus(t):
            return rec(t.arg1) + " + " + rec(t.arg)
        elif int.is_uminus(t):
            return "- " + rec(t.arg)
        elif int.is_minus(t):
            return rec(t.arg1) + " - " + rec(t.arg)
        elif int.is_times(t):
            return rec(t.arg1) + " * " + rec(t.arg)
        elif int.is_binary_int(t):
            return str(int.from_binary_int(t))
        elif t.is_comb() and t.head.is_const():
            return t.head.name + "(" + ", ".join(rec(arg) for arg in t.args) + ")"
        elif t.is_var() or t.is_const():
            return t.name
        else:
            print("Cannot print term with head:", repr(t.head))
            raise NotImplementedError

    return rec(t)

class Identifier():
    """Base class for identifiers: variables, entries of arrays, etc."""
    pass

class VariableId(Identifier):
    """Variables, specified by name."""
    def __init__(self, name):
        assert isinstance(name, str), "VariableId"
        self.name = name

    def __str__(self):
        return self.name

class ArrayId(Identifier):
    """Array identifier: an identifier followed by integer index."""
    def __init__(self, a, n):
        assert isinstance(a, Identifier) and isinstance(n, Term), "ArrayId"
        self.a = a
        self.n = n

    def __str__(self):
        return str(self.a) + "[" + print_term(self.n) + "]"

class FieldId(Identifier):
    """Field identifier: an identifier followed by a field name."""
    def __init__(self, a, fname):
        assert isinstance(a, Identifier) and isinstance(fname, str), "FieldId"
        self.a = a
        self.fname = fname

    def __str__(self):
        return str(self.a) + "." + self.fname

class Com():
    """Base class for programs."""
    def __init__(self):
        self.pre = []
        self.post = []

    def get_vc_pre(self):
        res = []
        for i in range(len(self.pre) - 1):
            res.append(Term.mk_implies(self.pre[i], self.pre[i+1]))
        return res

    def print_vc_pre(self):
        res = ""
        for t in self.get_vc_pre():
            res = res + "<" + print_term(t) + ">\n"
        return res

    def get_vc_post(self):
        res = []
        for i in range(len(self.post) - 1):
            res.append(Term.mk_implies(self.post[i], self.post[i+1]))
        return res

    def print_vc_post(self):
        res = ""
        for t in self.get_vc_post():
            res = res + "\n<" + print_term(t) + ">"
        return res

    def compute_wp(self, post):
        """Given post-condition for a command, find the pre-condition
        and verification conditions.

        """
        raise NotImplementedError

class Skip(Com):
    """Skip program."""
    def __init__(self):
        super().__init__()

    def print_com(self, thy):
        return self.print_vc_pre() + "skip"

    def get_vc(self):
        return self.get_vc_pre()

    def compute_wp(self, post):
        self.post = [post]
        self.pre.append(post)
        return self.pre[0]

class Assign(Com):
    """Assign program."""
    def __init__(self, v, e):
        if isinstance(v, str):
            v = VariableId(v)
        assert isinstance(v, Identifier) and isinstance(e, Term), "Assign"
        super().__init__()
        self.v = v
        self.e = e

    def print_com(self, thy):
        return self.print_vc_pre() + \
            str(self.v) + " := " + print_term(self.e)

    def get_vc(self):
        return self.get_vc_pre()

    def compute_wp(self, post):
        if isinstance(self.v, VariableId):
            self.post = [post]
            self.pre.append(post.subst({self.v.name: self.e}))
            return self.pre[0]
        else:
            raise NotImplementedError

class Seq(Com):
    """Sequence program."""
    def __init__(self, c1, c2):
        assert isinstance(c1, Com) and isinstance(c2, Com), "Seq"
        super().__init__()
        self.c1 = c1
        self.c2 = c2

    def print_com(self, thy):
        return self.print_vc_pre() + \
            self.c1.print_com(thy) + ";\n" + self.c2.print_com(thy)

    def get_vc(self):
        return self.get_vc_pre() + self.c1.get_vc() + self.c2.get_vc()

    def compute_wp(self, post):
        self.post = [post]
        mid = self.c2.compute_wp(post)
        pre = self.c1.compute_wp(mid)
        self.pre.append(pre)
        return self.pre[0]

class Cond(Com):
    """Conditional program."""
    def __init__(self, b, c1, c2):
        assert isinstance(b, Term) and isinstance(c1, Com) and isinstance(c2, Com), "Cond"
        super().__init__()
        self.b = b
        self.c1 = c1
        self.c2 = c2

    def compute_wp(self, post):
        self.post = [post]
        pre_c1 = self.c1.compute_wp(post)
        pre_c2 = self.c2.compute_wp(post)
        self.pre.append(logic.mk_if(self.b, pre_c1, pre_c2))
        return self.pre[0]

    def get_vc(self):
        return self.get_vc_pre() + self.c1.get_vc() + self.c2.get_vc()

    def print_com(self, thy):
        return self.print_vc_pre() + \
            "if (%s) then\n  %s\nelse\n  %s" % (
            print_term(self.b), self.c1.print_com(thy), self.c2.print_com(thy))

class While(Com):
    """While program."""
    def __init__(self, b, inv, c):
        assert isinstance(b, Term) and isinstance(inv, Term) and isinstance(c, Com), "While"
        super().__init__()
        self.b = b
        self.inv = inv
        self.c = c

    def compute_wp(self, post):
        self.pre.append(self.inv)
        self.c.pre = [logic.mk_conj(self.inv, self.b)] + self.c.pre
        self.c.compute_wp(self.inv)
        self.post = [logic.mk_conj(self.inv, logic.neg(self.b)), post]
        return self.pre[0]

    def get_vc(self):
        return self.get_vc_pre() + self.c.get_vc() + self.get_vc_post()

    def print_com(self, thy):
        cmd = self.c.print_com(thy).split('\n')
        cmd = '\n  '.join(cmd)
        return self.print_vc_pre() + "while (%s) {\n  [%s]\n  %s\n}" % (
            print_term(self.b), print_term(self.inv), cmd) + \
            self.print_vc_post()
