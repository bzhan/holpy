# Author: Bohua Zhan

"""Basic data structure for programs."""

from kernel.term import Term, Var
from logic import logic
from data import int
from imperative import expr


class Com():
    """Base class for programs."""
    def __init__(self):
        self.pre = []
        self.post = []

    def get_vc_pre(self):
        res = []
        for i in range(len(self.pre) - 1):
            res.append(expr.implies(self.pre[i], self.pre[i+1]))
        return res

    def print_vc_pre(self):
        res = ""
        for t in self.get_vc_pre():
            res = res + "<" + str(t) + ">\n"
        return res

    def get_vc_post(self):
        res = []
        for i in range(len(self.post) - 1):
            res.append(expr.implies(self.post[i], self.post[i+1]))
        return res

    def print_vc_post(self):
        res = ""
        for t in self.get_vc_post():
            res = res + "\n<" + str(t) + ">"
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
            v = expr.Var(v)
        assert isinstance(v, expr.Expr) and v.is_ident and isinstance(e, expr.Expr), "Assign"
        super().__init__()
        self.v = v
        self.e = e

    def print_com(self, thy):
        return self.print_vc_pre() + str(self.v) + " := " + str(self.e)

    def get_vc(self):
        return self.get_vc_pre()

    def compute_wp(self, post):
        if isinstance(self.v, expr.Var):
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
        assert isinstance(b, expr.Expr) and isinstance(c1, Com) and isinstance(c2, Com), "Cond"
        super().__init__()
        self.b = b
        self.c1 = c1
        self.c2 = c2

    def compute_wp(self, post):
        self.post = [post]
        pre_c1 = self.c1.compute_wp(post)
        pre_c2 = self.c2.compute_wp(post)
        self.pre.append(expr.ITE(self.b, pre_c1, pre_c2))
        return self.pre[0]

    def get_vc(self):
        return self.get_vc_pre() + self.c1.get_vc() + self.c2.get_vc()

    def print_com(self, thy):
        return self.print_vc_pre() + \
            "if (%s) then\n  %s\nelse\n  %s" % (
            str(self.b), self.c1.print_com(thy), self.c2.print_com(thy))

class While(Com):
    """While program."""
    def __init__(self, b, inv, c):
        assert isinstance(b, expr.Expr) and isinstance(inv, expr.Expr) and isinstance(c, Com), "While"
        super().__init__()
        self.b = b
        self.inv = inv
        self.c = c

    def compute_wp(self, post):
        self.pre.append(self.inv)
        self.c.pre = [expr.conj(self.inv, self.b)] + self.c.pre
        self.c.compute_wp(self.inv)
        self.post = [expr.conj(self.inv, expr.neg(self.b)), post]
        return self.pre[0]

    def get_vc(self):
        return self.get_vc_pre() + self.c.get_vc() + self.get_vc_post()

    def print_com(self, thy):
        cmd = self.c.print_com(thy).split('\n')
        cmd = '\n  '.join(cmd)
        return self.print_vc_pre() + "while (%s) {\n  [%s]\n  %s\n}" % (
            str(self.b), str(self.inv), cmd) + self.print_vc_post()
