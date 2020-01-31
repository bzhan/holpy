# Author: Bohua Zhan

import contextlib

from kernel.term import Var
from kernel.theory import Theory
from logic import basic
from syntax import parser


class Context:
    def __init__(self, *, svars=None, vars=None, defs=None):
        self.svars = dict()
        if svars is not None:
            for nm, T in svars.items():
                if isinstance(T, str):
                    T = parser.parse_type(T)
                self.svars[nm] = T

        self.vars = dict()
        if vars is not None:
            for nm, T in vars.items():
                if isinstance(T, str):
                    T = parser.parse_type(T)
                self.vars[nm] = T

        self.defs = dict()
        if defs is not None:
            for nm, T in defs.items():
                if isinstance(T, str):
                    T = parser.parse_type(T)
                self.defs[nm] = T

    def __eq__(self, other):
        return self.vars == other.vars and self.svars == other.svars and self.defs == other.defs

    def __str__(self):
        return 'vars: %s' % str(self.vars)

    def __repr__(self):
        return str(self)

    def get_vars(self):
        return [Var(nm, T) for nm, T in self.vars.items()]


"""Global context"""
ctxt = Context()

@contextlib.contextmanager
def fresh_context(*, svars=None, vars=None, defs=None):
    # Record previous context
    global ctxt
    prev_ctxt = ctxt

    # Set fresh context
    ctxt = Context(svars=svars, vars=vars, defs=defs)
    try:
        yield None
    finally:
        # Recover previous context
        ctxt = prev_ctxt

def set_context(thy_name, *, limit=None, username="master", svars=None, vars=None, defs=None):
    """Set theory and context (usually for testing).
    
    Parameters
    ==========

    thy_name : str or None
        Name of the theory. If None, theory is not changed.

    """
    # Set theory
    if thy_name is not None:
        basic.load_theory(thy_name, limit=limit, username=username)

    # Set context
    global ctxt
    ctxt = Context(svars=svars, vars=vars, defs=defs)
