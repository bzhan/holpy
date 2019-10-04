# Author: Bohua Zhan

"""Basic data structure for commands."""

from kernel.term import Term, Var
from logic import logic
from data import int
from imperative import expr


class Com():
    """Base class for commands.
    
    There are five basic types of commands: Skip, Assign, Seq, Cond
    and While, represented by sub-classes to be defined below.
    
    """
    def __init__(self):
        """Each command is associated with a sequence of preconditions
        and a sequence of postconditions. Let the preconditions be
        P_1, ..., P_n and the postconditions be Q_1, ..., Q_n, then
        <P_n> c <Q_1> is the Hoare triple derived directly from the
        Hoare rules, <P_1> c <Q_n> is the Hoare triple exposed to the
        outside, and P_1 --> P_2, ... and Q_1 --> Q_2, ... are the
        verification conditions.

        """
        self.pre = []
        self.post = []

    def get_vc_pre(self):
        """Return the verification conditions corresponding to the
        preconditions.

        """
        res = []
        for i in range(len(self.pre) - 1):
            res.append(expr.implies(self.pre[i], self.pre[i+1]))
        return res

    def print_vc_pre(self):
        """Print the verification conditions corresponding to the
        preconditions.

        """
        res = ""
        for t in self.get_vc_pre():
            res = res + "<" + str(t) + ">\n"
        return res

    def get_vc_post(self):
        """Return the verification conditions corresponding to the
        postconditions.

        """
        res = []
        for i in range(len(self.post) - 1):
            res.append(expr.implies(self.post[i], self.post[i+1]))
        return res

    def print_vc_post(self):
        """Print the verification conditions corresponding to the
        postconditions.

        """
        res = ""
        for t in self.get_vc_post():
            res = res + "\n<" + str(t) + ">"
        return res

    def compute_wp(self, post):
        """Given postcondition for a command, find the weakest
        precondition (wp) and verification conditions. Returns
        the weakest precondition for the command.

        """
        if isinstance(self, Skip):
            # <Q> Skip <Q>
            self.post = [post]
            self.pre.append(post)

        elif isinstance(self, Assign):
            if isinstance(self.v, expr.Var):
                # <Q[x := e]> x := e <Q>
                self.post = [post]
                self.pre.append(post.subst({self.v.name: self.e}))
            else:
                raise NotImplementedError

        elif isinstance(self, Seq):
            #  <P> c1 <R>
            #  <R> c2 <Q>
            # --------------
            # <P> c1; c2 <Q>
            self.post = [post]
            mid = self.c2.compute_wp(post)
            pre = self.c1.compute_wp(mid)
            self.pre.append(pre)

        elif isinstance(self, Cond):
            #    <P1> c1 <Q>
            #    <P2> c2 <Q>
            # -----------------------------------------------
            # <if b then P1 else P2> if b then c1 else c2 <Q>
            self.post = [post]
            pre_c1 = self.c1.compute_wp(post)
            pre_c2 = self.c2.compute_wp(post)
            self.pre.append(expr.ITE(self.b, pre_c1, pre_c2))

        elif isinstance(self, While):
            # Original rule is:
            #  <I & b> c <I>
            # -----------------
            # <I> while b do c <I & ~b>
            # From this, can derive:
            #  <I & b> c <I>
            #  I & ~b --> Q
            # -----------------
            # <I> while b do c <Q>
            self.pre.append(self.inv)
            self.c.pre = [expr.conj(self.inv, self.b)] + self.c.pre
            self.c.compute_wp(self.inv)
            self.post = [expr.conj(self.inv, expr.neg(self.b)), post]

        else:
            raise TypeError

        return self.pre[0]

    def print_com(self, thy):
        if isinstance(self, Skip):
            return self.print_vc_pre() + "skip"
        elif isinstance(self, Assign):
            return self.print_vc_pre() + str(self.v) + " := " + str(self.e)
        elif isinstance(self, Seq):
            return self.print_vc_pre() + \
                self.c1.print_com(thy) + ";\n" + self.c2.print_com(thy)
        elif isinstance(self, Cond):
            return self.print_vc_pre() + \
                "if (%s) then\n  %s\nelse\n  %s" % (
                str(self.b), self.c1.print_com(thy), self.c2.print_com(thy))
        elif isinstance(self, While):
            cmd = self.c.print_com(thy).split('\n')
            cmd = '\n  '.join(cmd)
            return self.print_vc_pre() + "while (%s) {\n  [%s]\n  %s\n}" % (
                str(self.b), str(self.inv), cmd) + self.print_vc_post()
        else:
            raise TypeError

    def get_vc(self):
        if isinstance(self, (Skip, Assign)):
            return self.get_vc_pre()
        elif isinstance(self, (Seq, Cond)):
            return self.get_vc_pre() + self.c1.get_vc() + self.c2.get_vc()
        elif isinstance(self, While):
            return self.get_vc_pre() + self.c.get_vc() + self.get_vc_post()
        else:
            raise TypeError


class Skip(Com):
    """Skip program."""
    def __init__(self):
        super().__init__()

class Assign(Com):
    """Assign program."""
    def __init__(self, v, e):
        if isinstance(v, str):
            v = expr.Var(v)
        assert isinstance(v, expr.Expr) and v.is_ident and isinstance(e, expr.Expr), "Assign"
        super().__init__()
        self.v = v
        self.e = e

class Seq(Com):
    """Sequence program."""
    def __init__(self, c1, c2):
        assert isinstance(c1, Com) and isinstance(c2, Com), "Seq"
        super().__init__()
        self.c1 = c1
        self.c2 = c2

class Cond(Com):
    """Conditional program."""
    def __init__(self, b, c1, c2):
        assert isinstance(b, expr.Expr) and isinstance(c1, Com) and isinstance(c2, Com), "Cond"
        super().__init__()
        self.b = b
        self.c1 = c1
        self.c2 = c2

class While(Com):
    """While program."""
    def __init__(self, b, inv, c):
        assert isinstance(b, expr.Expr) and isinstance(inv, expr.Expr) and isinstance(c, Com), "While"
        super().__init__()
        self.b = b
        self.inv = inv
        self.c = c
