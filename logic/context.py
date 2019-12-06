from kernel.term import Var
from kernel.theory import Theory
from syntax import parser


class Context:
    def __init__(self, thy, *, svars=None, vars=None, defs=None, limit=None):
        if isinstance(thy, str):
            from logic import basic
            self.thy = basic.load_theory(thy, limit=limit)
        else:
            assert isinstance(thy, Theory)
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

        self.defs = dict()
        if defs is not None:
            for nm, T in defs.items():
                if isinstance(T, str):
                    T = parser.parse_type(self.thy, T)
                self.defs[nm] = T

    def __eq__(self, other):
        return self.thy == other.thy and self.vars == other.vars and self.svars == other.svars and \
            self.defs == other.defs

    def get_vars(self):
        return [Var(nm, T) for nm, T in self.vars.items()]
