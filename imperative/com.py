# Author: Bohua Zhan

"""Basic data structure for programs."""

from kernel.term import Term
from syntax import printer

class Com():
    """Base class for programs."""
    pass

class Skip(Com):
    """Skip program."""
    def __init__(self):
        pass

    def print_com(self, thy):
        return "skip"

class Assign(Com):
    """Assign program."""
    def __init__(self, v, e):
        assert isinstance(v, str) and isinstance(e, Term), "Assign"
        self.v = v
        self.e = e

    def print_com(self, thy):
        return self.v + " := " + printer.print_term(thy, self.e)

class Seq(Com):
    """Sequence program."""
    def __init__(self, c1, c2):
        assert isinstance(c1, Com) and isinstance(c2, Com), "Seq"
        self.c1 = c1
        self.c2 = c2

    def print_com(self, thy):
        return self.c1.print_com(thy) + ";\n  " + self.c2.print_com(thy) + ';'

class Cond(Com):
    """Conditional program."""
    def __init__(self, b, c1, c2):
        assert isinstance(b, Term) and isinstance(c1, Com) and isinstance(c2, Com), "Cond"
        self.b = b
        self.c1 = c1
        self.c2 = c2

    def print_com(self, thy):
        return "if (%s) then\n  %s\nelse\n  %s" % (
            printer.print_term(thy, self.b), self.c1.print_com(thy), self.c2.print_com(thy))

class While(Com):
    """While program."""
    def __init__(self, b, inv, c):
        assert isinstance(b, Term) and isinstance(inv, Term) and isinstance(c, Com), "While"
        self.b = b
        self.inv = inv
        self.c = c

    def print_com(self, thy):
        return "while (%s) {\n  [%s]\n  %s\n}" % (
            printer.print_term(thy, self.b), printer.print_term(thy, self.inv), self.c.print_com(thy))
