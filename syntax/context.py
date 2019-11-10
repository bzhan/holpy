"""Context for parsing terms and proving."""

from kernel.term import Var
from kernel import theory


class Context:
    def __init__(self, thy, *, svars=None, vars=None, consts=None, limit=None):
        from logic import basic
        from syntax import parser
        if isinstance(thy, str):
            self.thy = basic.load_theory(thy, limit=limit)
        else:
            assert isinstance(thy, theory.Theory)
            self.thy = thy

        self.svars = dict()
        if svars is not None:
            for nm, T in svars.items():
                if isinstance(T, str):
                    T = parser.parse_type(self.thy, T)
                self.svars[nm] = T

        self.vars = dict()
        if vars is not None:
            for nm, T in vars.items():
                if isinstance(T, str):
                    T = parser.parse_type(self.thy, T)
                self.vars[nm] = T

        self.consts = dict()
        if consts is not None:
            for nm, T in consts.items():
                if isinstance(T, str):
                    T = parser.parse_type(self.thy, T)
                self.consts[nm] = T

    def __eq__(self, other):
        return self.thy == other.thy and self.vars == other.vars and self.consts == other.consts

    def get_vars(self):
        return [Var(nm, T) for nm, T in self.vars.items()]
