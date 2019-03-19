"""
Tseitin encoding from formulae in holpy to CNF.
"""

from collections import OrderedDict

from kernel.type import hol_bool
from kernel.term import Term, Var
from kernel.thm import Thm
from logic import basic
from logic import logic
from logic.proofterm import ProofTerm
from logic import logic_macro
from logic.conv import rewr_conv, rewr_conv_thm, every_conv, top_conv

thy = basic.loadTheory('sat')

conj = logic.mk_conj
disj = logic.mk_disj
neg = logic.neg
imp = Term.mk_implies
eq = Term.mk_equals


class EncodingException(Exception):
    pass


def logic_subterms(t):
    """Returns the list of logical subterms for a term t."""
    if t.is_implies() or t.is_equals() or logic.is_conj(t) or logic.is_disj(t):
        return logic_subterms(t.arg1) + logic_subterms(t.arg) + [t]
    elif logic.is_neg(t):
        return logic_subterms(t.arg) + [t]
    else:
        return [t]

def encode_eq_conj(l, r1, r2):
    """Encoding for the term l = (r1 & r2)."""
    return [disj(neg(l), r1), disj(neg(l), r2), disj(neg(r1), neg(r2), l)]

def encode_eq_disj(l, r1, r2):
    """Encoding for the term l = (r1 | r2)."""
    return [disj(neg(l), r1, r2), disj(neg(r1), l), disj(neg(r2), l)]

def encode_eq_imp(l, r1, r2):
    """Encoding for the term l = (r1 --> r2)."""
    return [disj(neg(l), neg(r1), r2), disj(r1, l), disj(neg(r2), l)]

def encode_eq_eq(l, r1, r2):
    """Encoding for the term l = (r1 = r2)."""
    return [disj(neg(l), neg(r1), r2), disj(neg(l), r1, neg(r2)), disj(l, neg(r1), neg(r2)), disj(l, r1, r2)]

def encode_eq_neg(l, r):
    """Encoding for the term l = ~r."""
    return [disj(l, r), disj(neg(l), neg(r))]

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
    As, F = th.assums[:-1], th.assums[-1]

    # Obtain the assumptions
    ptAs = [ProofTerm.assume(A) for A in As]
    ptF = ProofTerm.assume(F)

    # Obtain the expansion of each As to a non-atomic term.
    pts = []
    for ptA in ptAs:
        rhs = ptA.th.concl.arg
        if logic.is_conj(rhs):
            cv = rewr_conv_thm(thy, "encode_conj")
        elif logic.is_disj(rhs):
            cv = rewr_conv_thm(thy, "encode_disj")
        elif rhs.is_implies():
            cv = rewr_conv_thm(thy, "encode_imp")
        elif rhs.is_equals():
            cv = rewr_conv_thm(thy, "encode_eq")
        elif logic.is_neg(rhs):
            cv = rewr_conv_thm(thy, "encode_not")
        else:
            cv = None

        if cv:
            pts.append(cv.apply_to_pt(thy, ptA))

    # Obtain the rewrite of the original formula.
    cvs = [top_conv(rewr_conv(ProofTerm.symmetric(ptA), match_vars=False)) for ptA in ptAs]
    cv = every_conv(*cvs)

    pts.append(cv.apply_to_pt(thy, ptF))

    pt = pts[0]
    for pt2 in pts[1:]:
        pt = logic_macro.apply_theorem(thy, 'conjI', pt, pt2)

    return logic.norm_conj_assoc().apply_to_pt(thy, pt)

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
        return Var("x" + str(i+1), hol_bool)

    # Obtain the results:
    # eqs -- list of equality assumptions
    # clauses -- list of clauses
    eqs = []
    clauses = []
    for i, st in enumerate(subterms):
        l = get_var(i)
        if st.is_implies() or st.is_equals() or logic.is_conj(st) or logic.is_disj(st):
            r1 = get_var(subterms_dict[st.arg1])
            r2 = get_var(subterms_dict[st.arg])
            f = st.get_head()
            eqs.append(Term.mk_equals(l, f(r1, r2)))
            if st.is_implies():
                clauses.extend(encode_eq_imp(l, r1, r2))
            elif st.is_equals():
                clauses.extend(encode_eq_eq(l, r1, r2))
            elif logic.is_conj(st):
                clauses.extend(encode_eq_conj(l, r1, r2))
            else:  # st.is_disj()
                clauses.extend(encode_eq_disj(l, r1, r2))
        elif logic.is_neg(st):
            r = get_var(subterms_dict[st.arg])
            eqs.append(Term.mk_equals(l, logic.neg(r)))
            clauses.extend(encode_eq_neg(l, r))
        else:
            eqs.append(Term.mk_equals(l, st))

    clauses.append(get_var(len(subterms) - 1))

    # Final proposition: under the equality assumptions and the original
    # term t, can derive the conjunction of the clauses.
    th = Thm(eqs + [t], logic.mk_conj(*clauses))

    # Final CNF: for each clause, get the list of disjuncts.
    cnf = []
    def literal(t):
        if logic.is_neg(t):
            return (t.arg.name, False)
        else:
            return (t.name, True)

    for clause in clauses:
        cnf.append(list(literal(t) for t in logic.strip_disj(clause)))

    return cnf, th
