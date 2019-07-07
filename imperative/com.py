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
        elif int.is_less_eq(t):
            return rec(t.arg1) + " <= " + rec(t.arg)
        elif int.is_less(t):
            return rec(t.arg1) + " < " + rec(t.arg)
        elif int.is_plus(t):
            return rec(t.arg1) + " + " + rec(t.arg)
        elif int.is_minus(t):
            return rec(t.arg1) + " - " + rec(t.arg)
        elif int.is_times(t):
            return rec(t.arg1) + " * " + rec(t.arg)
        elif int.is_binary_int(t):
            return str(int.from_binary_int(t))
        elif t.is_var() or t.is_const():
            return t.name
        else:
            print("Cannot print term with head:", repr(t.head))
            raise NotImplementedError

    return rec(t)

class Com():
    """Base class for programs."""
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

class Skip(Com):
    """Skip program."""
    def __init__(self):
        self.pre = []

    def print_com(self, thy):
        return self.print_vc_pre() + "skip"

    def get_vc(self):
        return self.get_vc_pre()

    def compute_wp(self, post):
        self.post = post
        self.pre.append(post)
        return self.pre[-1]

class Assign(Com):
    """Assign program."""
    def __init__(self, v, e):
        assert isinstance(v, str) and isinstance(e, Term), "Assign"
        self.v = v
        self.e = e
        self.pre = []

    def print_com(self, thy):
        return self.print_vc_pre() + \
            self.v + " := " + print_term(self.e)

    def get_vc(self):
        return self.get_vc_pre()

    def compute_wp(self, post):
        self.post = post
        self.pre.append(post.subst({self.v: self.e}))
        return self.pre[-1]

class Seq(Com):
    """Sequence program."""
    def __init__(self, c1, c2):
        assert isinstance(c1, Com) and isinstance(c2, Com), "Seq"
        self.c1 = c1
        self.c2 = c2
        self.pre = []

    def print_com(self, thy):
        return self.print_vc_pre() + \
            self.c1.print_com(thy) + ";\n" + self.c2.print_com(thy)

    def get_vc(self):
        return self.get_vc_pre() + self.c1.get_vc() + self.c2.get_vc()

    def compute_wp(self, post):
        self.post = post
        mid = self.c2.compute_wp(post)
        self.pre.append(self.c1.compute_wp(mid))
        return self.pre[-1]

class Cond(Com):
    """Conditional program."""
    def __init__(self, b, c1, c2):
        assert isinstance(b, Term) and isinstance(c1, Com) and isinstance(c2, Com), "Cond"
        self.b = b
        self.c1 = c1
        self.c2 = c2
        self.pre = []

    def print_com(self, thy):
        return self.print_vc_pre() + \
            "if (%s) then\n  %s\nelse\n  %s" % (
            print_term(self.b), self.c1.print_com(thy), self.c2.print_com(thy))

class While(Com):
    """While program."""
    def __init__(self, b, inv, c):
        assert isinstance(b, Term) and isinstance(inv, Term) and isinstance(c, Com), "While"
        self.b = b
        self.inv = inv
        self.c = c
        self.pre = []

    def print_com(self, thy):
        cmd = self.c.print_com(thy).split('\n')
        cmd = '\n  '.join(cmd)
        return "while (%s) {\n  [%s]\n  %s\n}" % (
            print_term(self.b), print_term(self.inv), cmd)