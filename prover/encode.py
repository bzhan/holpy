"""
Tseitin encoding from formulae in holpy to CNF.
"""

from kernel.type import BoolType
from kernel.term import Term, Var, And, Or, Not, Implies, Eq
from kernel.thm import Thm
from kernel import term_ord
from kernel.proofterm import ProofTerm
from logic import basic
from logic import logic
from logic.conv import rewr_conv, every_conv, top_conv


def is_logical(t):
    return t.is_implies() or t.is_equals() or t.is_conj() or t.is_disj() or t.is_not()

def logic_subterms(t):
    """Returns the list of logical subterms for a term t."""
    def rec(t):
        if not is_logical(t):
            return [t]
        elif t.is_not():
            return rec(t.arg) + [t]
        else:
            return rec(t.arg1) + rec(t.arg) + [t]

    return term_ord.sorted_terms(rec(t))

def tseitin_encode(t):
    """Given a propositional formula t, compute its Tseitin encoding.

    The theorem is structured as follows:

    Each of the assumptions, except the last, is an equality, where
    the right side is either an atom or a logical operation between
    atoms. We call these assumptions As.

    The last assumption is the original formula. We call it F.

    The conclusion is in CNF. Each clause except the last is an
    expansion of one of As. The last clause is obtained by performing
    substitutions of As on F.

    """
    # Mapping from subterms to newly introduced variables
    subterm_dict = dict()
    for i, subt in enumerate(logic_subterms(t)):
        subterm_dict[subt] = Var('x' + str(i+1), BoolType)

    # Collect list of equations
    eqs = []
    for subt in subterm_dict:
        r = subterm_dict[subt]
        if not is_logical(subt):
            eqs.append(Eq(r, subt))
        elif subt.is_not():
            r1 = subterm_dict[subt.arg]
            eqs.append(Eq(r, Not(r1)))
        else:
            r1 = subterm_dict[subt.arg1]
            r2 = subterm_dict[subt.arg]
            eqs.append(Eq(r, subt.head(r1, r2)))

    # Form the proof term
    eq_pts = [ProofTerm.assume(eq) for eq in eqs]
    encode_pt = ProofTerm.assume(t)
    for eq_pt in eq_pts:
        encode_pt = encode_pt.on_prop(top_conv(rewr_conv(eq_pt, sym=True)))
    for eq_pt in eq_pts:
        if is_logical(eq_pt.rhs):
            encode_pt = logic.apply_theorem('conjI', eq_pt, encode_pt)
    
    # Rewrite using Tseitin rules
    encode_thms = ['encode_conj', 'encode_disj', 'encode_imp', 'encode_eq', 'encode_not']

    for th in encode_thms:
        encode_pt = encode_pt.on_prop(top_conv(rewr_conv(th)))
    
    # Normalize the conjuncts
    return encode_pt.on_prop(logic.conj_norm())

def convert_cnf(t):
    """Convert a term to CNF form (as a list of lists of literals)."""
    def convert_literal(lit):
        if lit.is_not():
            return (lit.arg.name, False)
        else:
            return (lit.name, True)
        
    def convert_clause(clause):
        return [convert_literal(lit) for lit in clause.strip_disj()]

    return [convert_clause(clause) for clause in t.strip_conj()]
