"""
Tseitin encoding from formulae in holpy to CNF.
"""

from collections import OrderedDict

from kernel.type import boolT
from kernel.term import Term, Var, And, Or, Not, Implies
from kernel.thm import Thm
from logic import basic
from logic import logic
from logic.proofterm import ProofTerm
from logic.conv import rewr_conv, every_conv, top_conv

basic.load_theory('sat')


class EncodingException(Exception):
    pass


def logic_subterms(t):
    """Returns the list of logical subterms for a term t."""
    if t.is_implies() or t.is_equals() or t.is_conj() or t.is_disj():
        return logic_subterms(t.arg1) + logic_subterms(t.arg) + [t]
    elif t.is_not():
        return logic_subterms(t.arg) + [t]
    else:
        return [t]

def encode_eq_conj(l, r1, r2):
    """Encoding for the term l = (r1 & r2)."""
    return [Or(Not(l), r1), Or(Not(l), r2), Or(Not(r1), Not(r2), l)]

def encode_eq_disj(l, r1, r2):
    """Encoding for the term l = (r1 | r2)."""
    return [Or(Not(l), r1, r2), Or(Not(r1), l), Or(Not(r2), l)]

def encode_eq_imp(l, r1, r2):
    """Encoding for the term l = (r1 --> r2)."""
    return [Or(Not(l), Not(r1), r2), Or(r1, l), Or(Not(r2), l)]

def encode_eq_eq(l, r1, r2):
    """Encoding for the term l = (r1 = r2)."""
    return [Or(Not(l), Not(r1), r2), Or(Not(l), r1, Not(r2)), Or(l, Not(r1), Not(r2)), Or(l, r1, r2)]

def encode_eq_not(l, r):
    """Encoding for the term l = ~r."""
    return [Or(l, r), Or(Not(l), Not(r))]

def get_encode_proof(th):
    """Given resulting theorem for an encoding, obtain the proof
    of the theorem.

    The theorem is structured as follows:

    Each of the assumptions, except the last, is an equality, where
    the right side is either an atom or a logical operation between
    atoms. We call these assumptions As.

    The last assumption is the original formula. We call it F.

    The conclusion is in CNF. Each clause except the last is an
    expansion of one of As. The last clause is obtained by performing
    substitutions of As on F.

    """
    As, F = th.hyps[:-1], th.hyps[-1]

    # Obtain the assumptions
    ptAs = [ProofTerm.assume(A) for A in As]
    ptF = ProofTerm.assume(F)

    # Obtain the expansion of each As to a non-atomic term.
    pts = []
    for ptA in ptAs:
        rhs = ptA.prop.rhs
        if rhs.is_conj():
            pts.append(ptA.on_prop(rewr_conv("encode_conj")))
        elif rhs.is_disj():
            pts.append(ptA.on_prop(rewr_conv("encode_disj")))
        elif rhs.is_implies():
            pts.append(ptA.on_prop(rewr_conv("encode_imp")))
        elif rhs.is_equals():
            pts.append(ptA.on_prop(rewr_conv("encode_eq")))
        elif rhs.is_not():
            pts.append(ptA.on_prop(rewr_conv("encode_not")))

    # Obtain the rewrite of the original formula.
    cvs = [top_conv(rewr_conv(ProofTerm.symmetric(ptA))) for ptA in ptAs]
    cv = every_conv(*cvs)

    pts.append(ptF.on_prop(cv))

    pt = pts[0]
    for pt2 in pts[1:]:
        pt = logic.apply_theorem('conjI', pt, pt2)

    return pt.on_prop(logic.norm_conj_assoc())

def encode(t):
    """Convert a holpy term into an equisatisfiable CNF. The result
    is a pair (cnf, prop), where cnf is the CNF form, and prop is
    a theorem stating that t, together with equality assumptions,
    imply the statement in CNF.

    """
    # Find the list of logical subterms, remove duplicates.
    subterms = logic_subterms(t)
    subterms = list(OrderedDict.fromkeys(subterms))
    subterms_dict = dict()
    for i, st in enumerate(subterms):
        subterms_dict[st] = i

    # The subterm at index i corresponds to variable x(i+1).
    def get_var(i):
        return Var("x" + str(i+1), boolT)

    # Obtain the results:
    # eqs -- list of equality assumptions
    # clauses -- list of clauses
    eqs = []
    clauses = []
    for i, st in enumerate(subterms):
        l = get_var(i)
        if st.is_implies() or st.is_equals() or st.is_conj() or st.is_disj():
            r1 = get_var(subterms_dict[st.arg1])
            r2 = get_var(subterms_dict[st.arg])
            f = st.head
            eqs.append(Term.mk_equals(l, f(r1, r2)))
            if st.is_implies():
                clauses.extend(encode_eq_imp(l, r1, r2))
            elif st.is_equals():
                clauses.extend(encode_eq_eq(l, r1, r2))
            elif st.is_conj():
                clauses.extend(encode_eq_conj(l, r1, r2))
            else:  # st.is_disj()
                clauses.extend(encode_eq_disj(l, r1, r2))
        elif st.is_not():
            r = get_var(subterms_dict[st.arg])
            eqs.append(Term.mk_equals(l, Not(r)))
            clauses.extend(encode_eq_not(l, r))
        else:
            eqs.append(Term.mk_equals(l, st))

    clauses.append(get_var(len(subterms) - 1))

    # Final proposition: under the equality assumptions and the original
    # term t, can derive the conjunction of the clauses.
    th = Thm(eqs + [t], And(*clauses))

    # Final CNF: for each clause, get the list of disjuncts.
    cnf = []
    def literal(t):
        if t.is_not():
            return (t.arg.name, False)
        else:
            return (t.name, True)

    for clause in clauses:
        cnf.append(list(literal(t) for t in clause.strip_disj()))

    return cnf, th
