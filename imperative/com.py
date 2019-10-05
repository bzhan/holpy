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

    def compute_wp(self, post):
        """Given postcondition for a command, find the weakest
        precondition (wp) and verification conditions. Returns
        the weakest precondition for the command.

        """
        assert isinstance(post, expr.Expr), "compute_wp"

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

    def get_lines(self, vars):
        """Obtain lines for pretty-printing of the command. Each line
        is specified by its type (one of 'com', 'inv' and 'vc'), its
        indentation level, and the text. Lines of type 'vc' contains both
        the printed expression form and the printed HOL form.

        """
        lines = []
        indent = 0

        def add_vc(ls):
            """Add verification conditions for the specified list
            (either pre or post).

            """
            for i in range(len(ls) - 1):
                vc = expr.implies(ls[i], ls[i+1])
                vc_hol = vc.convert_hol(vars)
                lines.append({
                    'ty': 'vc',
                    'indent': indent,
                    'str': str(vc),
                    'vars': vars,
                    'prop': vc_hol
                })

        def add_line(line):
            lines.append({
                'ty': 'com',
                'indent': indent,
                'str': line
            })

        def add_inv(line):
            lines.append({
                'ty': 'inv',
                'indent': indent,
                'str': line
            })

        def add_str(s):
            assert len(lines) > 0
            lines[-1]['str'] += ';'

        def rec(cmd):
            nonlocal indent

            if isinstance(cmd, Skip):
                add_vc(cmd.pre)
                add_line("skip")

            elif isinstance(cmd, Assign):
                add_vc(cmd.pre)
                add_line(str(cmd.v) + " := " + str(cmd.e))

            elif isinstance(cmd, Seq):
                add_vc(cmd.pre)
                rec(cmd.c1)
                add_str(';')
                rec(cmd.c2)

            elif isinstance(cmd, Cond):
                add_vc(cmd.pre)
                add_line("if (%s) then" % str(cmd.b))
                indent += 2
                rec(cmd.c1)
                indent -= 2
                add_line("else")
                indent += 2
                rec(cmd.c2)
                indent -= 2

            elif isinstance(cmd, While):
                add_vc(cmd.pre)
                add_line("while (%s) {" % str(cmd.b))
                indent += 2
                add_inv("[%s]" % str(cmd.inv))
                rec(cmd.c)
                indent -= 2
                add_line("}")
                add_vc(cmd.post)

            else:
                raise TypeError

        rec(self)
        return lines

    def print_com(self, vars):
        """Obtain the pretty-printed version of the command."""
        lines = self.get_lines(vars)
        return list(l['indent'] * ' ' + l['str'] for l in lines)

    def get_vcs(self, vars):
        """Obtain the verification conditions as a list."""
        lines = self.get_lines(vars)
        return list(l['str'] for l in lines if l['ty'] == 'vc')


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
