"""
Implementation of Omega Test decision procedure.

Reference: implementation of Omega in HOL4
https://github.com/HOL-Theorem-Prover/HOL/blob/develop/src/integer/OmegaMLShadow.sml

"""

import collections
import functools
import copy
from math import gcd, ceil, floor

from kernel import term
from kernel import term_ord
from kernel import proofterm
from data import integer
from logic import logic, basic
from logic import conv

basic.load_theory('int')


class NoGCDException(Exception):
    """Indicates there are no gcd in current factoid."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class RedundantAdditionException(Exception):
    """Raised when there is already a factoid with less or equal constant in database."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class Factoid:
    """A factoid is represented by the list of coefficients c[0..n], meaning

    0 <= c[0] * v_0 + ... c[n-1] * v_{n-1} + c[n] * 1

    """
    def __init__(self, coeff):
        assert isinstance(coeff, collections.abc.Iterable) and \
            all(isinstance(i, int) for i in coeff) and len(coeff) > 0, "Invalid coefficients list"
        self.coeff = tuple(coeff)
    
    def __len__(self):
        return len(self.coeff)
    
    def __getitem__(self, pos):
        return self.coeff[pos]
    
    def __str__(self):
        return "0 <= " + " + ".join("%s * x%s" % (self.coeff[i], i) for i in range(len(self.coeff) - 1)) + " + " + str(self.coeff[-1])
    
    def __repr__(self):
        return str(self.coeff)
    
    def __hash__(self):
        if 0 <= self.coeff[0]:
            h = 0
            for i in range(len(self.coeff) - 1):
                h += (i+1) * self.coeff[i]
            return h
        else:
            return hash(Factoid([-n for n in self.coeff]))
    
    def __eq__(self, f):
        return self.coeff == f.coeff
    
    @property
    def key(self):
        """Return the variable coefficients."""
        return self.coeff[:-1]
    
    @property
    def constant(self):
        """Return the constant part."""
        return self.coeff[-1]
    
    def split_factoid(self):
        """Return (key, constant)"""
        if len(self.coeff) >= 2:
            return (self.coeff[:-1], self.coeff[-1])
        else:
            return (None, self.coeff[-1])
        
    def is_zero_var_factoid(self):
        """If all coefficients are zero, return true."""
        return all(c == 0 for c in self.coeff[:-1])
    
    def is_false_factoid(self):
        """Return true if all coefficients are zeros and the constant < 0."""
        return self.is_zero_var_factoid() and self.constant < 0
    
    def is_true_factoid(self):
        """Return true if all coefficients are zeros and the constant >= 0."""
        return self.is_zero_var_factoid() and self.constant >= 0

    def eval_factoid_rhs(self, vmap):
        """vmap is an int->int map, use vmap to calculate the rhs."""
        s = 0
        for i in range(len(self.coeff) - 1):
            if self.coeff[i] != 0 and i in vmap.keys():
                s += self.coeff[i] * vmap[i]
                
        return s + self.coeff[-1]

    def eval_factoid_except(self, vmap, j):
        """
        vmap is an int->int map, use vmap to calculate the factoid value without the j'th var's value.
        Note j starts from 0.
        """
        s = 0
        for i in range(len(self.coeff) - 1):
            if self.coeff[i] != 0 and i in vmap.keys() and i != j:
                s += self.coeff[i] * vmap[i]
                
        return s + self.coeff[-1]
    
def negate_key(f):
    """Negate keys."""
    return Factoid([-k for k in f])
    
def lcm(a, b):
    """Return least common multiple"""
    return a * b / gcd(a, b)

def combine_real_factoid(i, f1, f2):
    """
    Combine two factoids by "variable elimination" on the i'th variable.
    
    The coefficient of v_i should be strictly positive in f1, and
    strictly negative in f2. The combination may produce a factoid where
    all coefficients can be divided by some factor.

    """
    assert f1[i] > 0 and f2[i] < 0 and i < len(f1) - 1, "combine_real_factoid"
    c0, d0 = f1[i], -f2[i]
    g = gcd(c0, d0)
    c, d = int(c0 / g), int(d0 / g)
    real_factoid = [c * n + d * m for m, n in zip(f1, f2)]
    return Factoid(real_factoid)

def combine_dark_factoid(i, f1, f2):
    """
    Combine two factoids to produce a "dark shadow" factoid.
    
    The coefficient of v_i should be strictly positive in f1, and
    strictly negative in f2.

    """
    assert f1[i] > 0 and f2[i] < 0 and i < len(f1) - 1, "combine_real_factoid"
    a, b = f1[i], -f2[i]
    dark_factoid = [a * n + b * m for m, n in zip(f1, f2)]
    dark_factoid[-1] = dark_factoid[-1] - (a - 1) * (b - 1)
    return Factoid(dark_factoid)

def term_to_factoid(vars, t):
    """
    Returns the factoid corresponding to a term t.

    Given t of the form
      0 <= c1 * v1 + ... + cn * vn + num
    Assumes that the variables are in the "correct" order (as given in the
    list vars), but are not necessarily all present. Omission indicates
    a coefficient of zero.
    
    """
    def mk_coeff(vlist, slist):
        if len(vlist) == 0 and len(slist) == 0:
            return [0]
        elif len(vlist) == 0 and len(slist) == 1:
            return [slist[0].dest_number()]
        elif len(vlist) == 0:
            raise ValueError
        elif len(vlist) > 0 and len(slist) == 0:
            return [0] + mk_coeff(vlist[1:], [])
        elif len(vlist) > 0 and len(slist) > 0:
            s, v = slist[0], vlist[0]
            if s.is_times():
                c, mv = integer.dest_times(s)
                if mv == v:
                    return [c.dest_number()] + mk_coeff(vlist[1:], slist[1:])
                else:
                    return [0] + mk_coeff(vlist[1:], slist)
            else:
                return [0] + mk_coeff(vlist[1:], slist)

    return Factoid(mk_coeff(vars, integer.strip_plus(t.arg)))

def factoid_to_term(vars, f):
    """
    Returns the term corresponding to f.
    
    Here vars is the list of variables.

    """
    return term.less_eq(term.IntType)(term.Int(0), sum([term.Int(c) * v for c, v in zip(f[1:-1], vars[1:])], term.Int(f[0]) * vars[0]) + term.Int(f[-1]))


class Derivation:
    """A derivation is a proof of a factoid."""
    pass

class ASM(Derivation):
    """Assumptions"""
    def __init__(self, t):
        self.t = t

    def __str__(self):
        return "ASM %s" % str(self.t)

    def __repr__(self):
        return str(self)

class RealCombine(Derivation):
    """Combining two factoids (inequalities)."""
    def __init__(self, i, deriv1, deriv2):
        self.i = i
        self.deriv1 = deriv1
        self.deriv2 = deriv2

    def __str__(self):
        return "\tREAL_COMBIN var %s:\n\t\t %s\n\t %s\n" % (str(self.i), str(self.deriv1), str(self.deriv2))

    def __repr__(self):
        return str(self)

class GCDCheck(Derivation):
    def __init__(self, deriv):
        self.deriv = deriv

    def __str__(self):
        return "GCD_CHECK: \n  %s\n" % str(self.deriv)

    def __repr__(self):
        return str(self)

class DirectContr(Derivation):
    def __init__(self, deriv1, deriv2):
        self.deriv1 = deriv1
        self.deriv2 = deriv2

    def __str__(self):
        return "DIRECT_CONTR: \n  %s\n  %s\n" % (str(self.deriv1), str(self.deriv2))

    def __repr__(self):
        return str(self)


# A factoid together with its derivation
dfactoid = collections.namedtuple('dfactoid', ['factoid', 'deriv'])

def split_dfactoid(df):
    """Given a factoid with a derivation, extract its key, constant,
    and derivation in a three-tuple.

    """
    return (df.factoid.key, df.factoid.constant, df.deriv)


class Result:
    """Result of the decision algorithm."""
    pass

class Contr(Result):
    def __init__(self, deriv):
        self.deriv = deriv

    def __str__(self):
        return "CONTR: %s" % str(self.deriv)
    
    def __repr__(self):
        return str(self)

class Satisfiable(Result):
    def __init__(self, *args, **kwargs):
        self.store = dict()
        if args is not None:
            self.store = dict(args[0])
        self.store.update(**kwargs)

    def __str__(self):
        return "SATISFIABLE: %s" % str(self.store)

    def __repr__(self):
        return str(self)

    def update(self, d):
        self.store.update(d)

class NoConcl(Result):
    def __init__(self):
        pass

    def __str__(self):
        return "NO_CONCL"

    def __repr__(self):
        return str(self)


"""
The elimination modes keeps track what sort of shadow we're currently
working on.

REAL when we're looking for a contradiction (only)
DARK when we're looking for satisfiability and the problem is not exact
EXACT when we're looking for either a contradiction or satisfiability.
EDARK when we're looking for satisfiability (i.e., have switched from
      a REAL search, but where the problem is still EXACT)

"""
REAL, DARK, EXACT, EDARK = range(4)


def inexactify(mode):
    if mode == EXACT:
        return REAL
    elif mode == EDARK:
        return DARK
    else:
        return mode

def mode_result(em, result):
    if em == EXACT:
        return result
    elif em == REAL:
        return NoConcl() if isinstance(result, Satisfiable) else result
    elif em in (DARK, EDARK):
        return NoConcl() if isinstance(result, Contr) else result

def combine_dfactoid(em, i, f1, d1, f2, d2):
    """Combine two factoids according to the current mode.
    
    em -- current mode
    i -- current variable
    f1, d1 -- first formula and derivation
    f2, d2 -- second formula and derivation

    """ 
    if em == DARK:
        return dfactoid(combine_dark_factoid(i, f1, f2), d1)
    else:
        return dfactoid(combine_real_factoid(i, f1, f2), RealCombine(i, d1, d2))

def insert_db(db, fk):
    hash_key = hash(fk.factoid)
    if hash_key in db.keys():
        db[hash_key].append(fk)
    else:
        db[hash_key] = [fk]

def lookup_fkey(db, fk):
    """Lookup a given key in database."""
    hash_key = hash(fk)
    if hash_key in db.keys():
        alist = db[hash_key]
        for df in alist:
            if df.factoid.key == fk.key:
                return df
        raise KeyError
    else:
        raise KeyError

def has_one_var(db):
    """
    returns true if all of ptree's factoids are over just one variable
    """
    index = -1
    has_var = False
    for _, dfs in db.items():
        for df in dfs:
            d, f = df.deriv, df.factoid
            for i, v in enumerate(f.key):
                if v != 0: 
                    if not has_var:
                        index = i
                        has_var = True
                    elif has_var and i != index:
                        return False
    return has_var

def find_var(db):
    """
    Precondition: db has only one var.
    Return the var.
    """
    for _, dfs in db.items():
        for df in dfs:
            f = df.factoid
            for index, k in enumerate(f.key):
                if k != 0:
                    return index

def one_var_analysis(db, em):
    """
    Precondition: the dfactoids in ptree have just one variable with a
    non-zero coefficient, and its everywhere the same variable.  Our aim
    is to either derive a contradiction, or to return a satisfying
    assignment.  Our gcd_checks will have ensured that our variable
    (call it x) will only have coefficients of one at this point, so
    we just need to check that the maximum of the lower bounds is less
    than or equal to the minimum of the lower bounds.  If it is then
    return either as a satisfying valuation for x.  Otherwise return
    false, combining the maximum lower and the minimum upper constraint.
    """
    x_var = find_var(db)
    upper, lower = None, None
    for _, dfs in db.items():
        for df in dfs:
            f = df.factoid
            fk, fc, d = split_dfactoid(df)
            for index, k in enumerate(f.key):
                if fk[x_var] < 0 and (upper is None or upper[0] > fc):
                    upper = (fc, d)
                elif fk[x_var] > 0 and (lower is None or lower[0] < -fc):
                    lower = (-fc, d)

    if upper is None and lower is None:
        raise ValueError
    elif upper is not None and lower is None:
        if em == REAL:
            return NoConcl()
        else:
            return Satisfiable({x_var:upper[0]})
    elif upper is None and lower is not None:
        if em == REAL:
            return NoConcl()
        else:
            return Satisfiable({x_var:lower[0]})
    else:
        u, du, l, dl = upper[0], upper[1], lower[0], lower[1]
        if u < l:
            if em in (DARK, EDARK):
                return NoConcl()
            else:
                return Contr(DirectContr(du, dl))
        else:
            if em == REAL:
                return NoConcl()
            else:
                return Satisfiable({x_var:u})

def exact_var(db, width):
    """
    An exact var is one that has coefficients of one in either all of its
    upper bounds or all of its lower bounds.  This function returns
    SOME v if v is an exact var in ptree, or NONE if there is no exact
    var.
    """
    up_coeffs_unit = [True] * (width - 1)
    low_coeffs_unit = [True] * (width - 1)
    coeffs_all_zero = [True] * (width - 1)

    for _, dfactoids in db.items():
        for df in dfactoids:
            f = df.factoid
            for i, ai in enumerate(f.key):
                if ai < 0:
                    if abs(ai) != 1:
                        up_coeffs_unit[i] = False
                    coeffs_all_zero[i] = False
                elif ai > 0:
                    if abs(ai) != 1:
                        low_coeffs_unit[i] = False
                    coeffs_all_zero[i] = False

    for i in range(width - 1):
        if low_coeffs_unit[i] and not coeffs_all_zero[i]:
            return i
    for i in range(width - 1):
        if up_coeffs_unit[i] and not coeffs_all_zero[i]:
            return i

    return None

def least_coeff_var(db, width):
    """
    Returns the variable whose coefficients' absolute values sum to the
    least amount (that isn't zero).
    """
    sums = [0] * (width - 1)
    for _, dfactoids in db.items():
        for df in dfactoids:
            f = df.factoid
            for i, ai in enumerate(f.key):
                sums[i] += abs(ai)
    
    def find_min(lst):
        pairs = sorted([(val, index) for index, val in enumerate(lst)])
        for el, index in pairs:
            if el != 0:
                return index

    return find_min(sums)

def extend_vmap(db, i, vmap):
    """
    vmap provides values for all of the variables present in ptree's
    factoids except i.  Use it to evaluate all of the factoids, except
    at variable i and to then return vmap extended with a value for
    variable i that respects all of the factoids.

    """
    lower, upper = None, None
    for _, dfactoids in db.items():
        for df in dfactoids:
            f = df.factoid
            c0 = f.eval_factoid_except(vmap, i)
            fk = f.key
            coeff = fk[i]

            if coeff < 0: #upper case
                c = floor(c0/(-coeff))
                if upper is None or c < upper:
                    upper = c
            
            elif coeff > 0: #lower case
                c = ceil(-(c0/(coeff)))
                if lower is None or c > lower:
                    lower = c
    
    assert lower <= upper
    
    vmap[i] = lower
    return vmap

def zero_upto(n):
    """
    Returns an integer map that maps the integers from 0..n (inclusive)
    to Arbint.zero.
    """
    assert n >= 0, "zero_upto need called negative number" 
    v = dict()
    for i in range(n + 1):
        v[i] = 0

    return v

def find_redundant_var(db, width):
    numvars = width - 1
    has_low, has_up = [False] * numvars, [False] * numvars
    for _, dfactoids in db.items():
        for df in dfactoids:
            fk = df.factoid.key
            for i, k in enumerate(fk):
                if k < 0:
                    has_up[i] = True
                elif k > 0:
                    has_low[i] = True
    
    for _, dfactoids in db.items():
        for df in dfactoids:
            fk = df.factoid.key
            for i, k in enumerate(fk):
                if has_low[i] != has_up[i]:
                    return (i, has_up[i])
    return None

def extend_cross_product(db, is_exact, i, lowers, uppers):
    """Extend db with the cross product between lowers and uppers"""
    for low in lowers:
        for up in uppers:
            # Combine the two
            f1, d1 = low.factoid, low.deriv
            f2, d2 = up.factoid, up.deriv
            if is_exact:
                df = dfactoid(combine_real_factoid(i, f1, f2), RealCombine(i, d1, d2))
            else:
                df = dfactoid(combine_dark_factoid(i, f1, f2), d1)

            # Reduce gcd
            g = functools.reduce(gcd, df.factoid[:-1])
            if g > 1:
                elim_gcd_factoid = [floor(i / g) for i in df.factoid]
                df = dfactoid(Factoid(elim_gcd_factoid), GCDCheck(df.deriv))

            if df.factoid.is_true_factoid():
                continue
            elif df.factoid.is_false_factoid():
                return Contr(df.deriv)
            else:
                f = df.factoid
                found_redundant, found_contra = None, None
                if hash(f) in db.keys():
                    for v in db[hash(f)]:
                        if v.factoid.key == f.key and v.factoid.constant <= f.constant:
                            found_redundant = True
                if hash(negate_key(f)) in db.keys():
                    for v in db[hash(negate_key(f))]:
                        if v.factoid.key == f.key and v.factoid.constant < -f.constant:
                            found_contra = v.deriv

                if found_redundant:
                    continue
                elif found_contra:
                    return Contr(DirectContr(df.deriv, found_contra))
                else:
                    insert_db(db, df)
                    
    return db

def solve(em, db, width):
    if isinstance(db, Contr):
        return db

    elif len(db) == 0:
        # Trivial case
        return Satisfiable(zero_upto(width - 2))

    elif has_one_var(db):
        # Only one variable
        r = one_var_analysis(db, em)
        return mode_result(em, r)

    elif find_redundant_var(db, width):
        # Has variable with only upper or lower bounds
        j, has_up = find_redundant_var(db, width)
        new_db = dict()
        elim = [] # store redundant factoids
        for _, dfactoids in db.items():
            for df in dfactoids:
                fk = df.factoid.key
                if fk[j] == 0:
                    insert_db(new_db, df)
                else:
                    elim.append(df)

        r = solve(em, new_db, width)
        if not isinstance(r, Satisfiable):
            return r

        vmap = r.store
        def mapthis(df):
            if has_up:
                return floor(-df.factoid.eval_factoid_except(vmap, j)/df.factoid[j])
            else:
                return ceil(-df.factoid.eval_factoid_except(vmap, j)/df.factoid[j])
        evaluated = [mapthis(df) for df in elim]
        if has_up:
            r.update({j:min(evaluated)})
        else:
            r.update({j:max(evaluated)})
        return r

    else:
        var_to_elim = exact_var(db, width)
        if var_to_elim:
            is_exact = True
            # print('exact elim %d' % var_to_elim)
        else:
            var_to_elim = least_coeff_var(db, width)
            is_exact = False
            # print('dark elim %d' % var_to_elim)

        lowers, uppers = [], []
        newdb = dict()
        for _, dfactoids in db.items():
            for df in dfactoids:
                f = df.factoid
                if f[var_to_elim] < 0:
                    uppers.append(df)
                elif f[var_to_elim] == 0:
                    insert_db(newdb, df)
                else:
                    lowers.append(df)

        def drop_contr(re):
            return NoConcl() if isinstance(re, Contr) else re

        def extend_satisfiable(r):
            if isinstance(r, Satisfiable):
                r2 = Satisfiable(extend_vmap(db, var_to_elim, r.store))
                return r2
            else:
                return r

        def db_exact():
            return extend_cross_product(copy.deepcopy(newdb), True, var_to_elim, lowers, uppers)

        def db_dark():
            return extend_cross_product(copy.deepcopy(newdb), False, var_to_elim, lowers, uppers)

        if em == EXACT:
            if is_exact:
                r = solve(EXACT, db_exact(), width)
                return extend_satisfiable(r)
            else:
                r = solve(REAL, db_exact(), width)
                if isinstance(r, Contr):
                    return r
                else:
                    r2 = solve(EDARK, db_dark(), width)
                    return drop_contr(extend_satisfiable(r2))
        elif em == REAL:
            return solve(REAL, db_exact(), width)
        elif em == EDARK:
            if is_exact:
                r = solve(EDARK, db_exact(), width)
                return drop_contr(extend_satisfiable(r))
            else:
                r = solve(DARK, db_dark(), width)
                return drop_contr(extend_satisfiable(r))
        else:  # em == DARK
            if is_exact:
                r = solve(DARK, db_exact(), width)
                return drop_contr(extend_satisfiable(r))
            else:
                r = solve(DARK, db_dark(), width)
                return drop_contr(extend_satisfiable(r))

def solve_matrix(matrix, mode=EXACT):
    """
    Give some factoids, return the result.
    """
    fs = [Factoid(f) for f in matrix]
    db = dict()
    for ft in fs:
        insert_db(db, dfactoid(ft, ASM(ft)))
    r = solve(EXACT, db, len(matrix[0]))
    if isinstance(r, Satisfiable):
        return "SAT", r.store
    elif isinstance(r, Contr):
        return "UNSAT", r
    elif isinstance(r, NoConcl):
        return "NOCONCL", None

def is_integer_ineq(tm):
    """
    Check tm is whether an integer inequlity term. 
    """
    return tm.is_compares() and tm.arg.get_type() == term.IntType and tm.arg1.get_type() == term.IntType

class OmegaHOL:
    """
    Handling omega test decision procedure in higher-order logic.
    """
    def __init__(self, ineqs):
        """
        Must guarantee the input inequalities are all integer terms.
        """
        assert isinstance(ineqs, collections.abc.Iterable) and all(is_integer_ineq(t) for t in ineqs)
        self.ineqs = ineqs
        
        # store all the normal form inequlities: 0 <= Σ ai * xi + c
        self.norm_pts = dict()
        self.norm_ineqs = list()
        occr_vars = set()
        for i in range(len(self.ineqs)):
            pt = proofterm.ProofTerm.assume(self.ineqs[i]).on_prop(integer.omega_form_conv())
            self.norm_pts[self.ineqs[i]] = pt
            self.norm_ineqs.append(pt.prop)
            occr_vars |= set(self.ineqs[i].get_vars())
        
        # store ordered vars
        self.vars = term_ord.sorted_terms(occr_vars)

        # convert inequalities to factoids
        self.factoids = [term_to_factoid(self.vars, t) for t in self.norm_ineqs]

        # mapping from factoids to HOL terms
        self.fact_hol = {f: factoid_to_term(self.vars, f) for f in self.factoids}

    def real_combine_pt(self, pt1, pt2, c1, c2):
        """
        pt1, pt2 are all proof terms which prop is a normal inequality,
        v is the variable index which will be elimated.
        c1, c2 are the coefficient pt1, pt2's prop need to multiply
        """
        def get_const_comp_pt(c):
            """
            c is a number, return a pt: c ⋈ 0
            """
            if c > 0:
                return proofterm.ProofTerm('int_const_ineq', term.greater(term.IntType)(term.Int(c), term.Int(0)))
            else:
                return proofterm.ProofTerm('int_const_ineq', term.less(term.IntType)(term.Int(c), term.Int(0)))
        
        def ineq_mul_const(c, pt):
            assert c != 0
            pt_c = get_const_comp_pt(c)
            if c > 0:
                return logic.apply_theorem('int_geq_zero_mul_pos', pt_c, pt)
            else:
                return logic.apply_theorem('int_geq_zero_mul_neg', pt_c, pt)
        
        pt1_mul_c1, pt2_mul_c2 = ineq_mul_const(c1, pt1), ineq_mul_const(c2, pt2)
        pt_final = logic.apply_theorem('int_pos_plus', pt1_mul_c1, pt2_mul_c2)
        return pt_final.on_prop(conv.arg_conv(integer.omega_simp_full_conv()))

    def gcd_pt(self, vars, pt):
        fact = term_to_factoid(vars, pt.prop)
        g = functools.reduce(gcd, fact[:-1])
        assert g > 1
        elim_gcd_fact = [floor(i / g) for i in fact]
        pt1 = proofterm.ProofTerm('int_const_ineq', term.Int(g) > term.Int(0))
        pt2 = pt
        elim_gcd_no_constant = sum([c * v for c, v in zip(elim_gcd_fact[1:-1], vars[1:])], elim_gcd_fact[0] * vars[0])
        original_no_constant = sum([c * v for c, v in zip(fact[1:-1], vars[1:])], fact[0] * vars[0])
        
        elim_gcd_no_constant = integer.int_norm_conv().get_proof_term(elim_gcd_no_constant).rhs
        original_no_constant = integer.int_norm_conv().get_proof_term(original_no_constant).rhs

        pt3 = integer.int_norm_conv().get_proof_term(g * elim_gcd_no_constant).transitive(
                    integer.int_norm_conv().get_proof_term(original_no_constant).symmetric())
        n = floor(-fact[-1] / g)
        pt4 = proofterm.ProofTerm('int_const_ineq', term.Int(g) * term.Int(n) + fact[-1] < 0)
        pt5 = proofterm.ProofTerm('int_const_ineq', term.Int(g) * (term.Int(n) + term.Int(1)) + fact[-1] > 0)
        pt6 = integer.int_eval_conv().get_proof_term(-(term.Int(n) + term.Int(1)))
        return logic.apply_theorem('int_gcd', pt1, pt2, pt3, pt4, pt5).on_prop(conv.top_sweep_conv(conv.rewr_conv(pt6)))
        
    def handle_unsat_result(self, res):
        
        def extract(f):
            if isinstance(f, ASM):
                return proofterm.ProofTerm.assume(self.fact_hol[f.t])
            else:
                return self.handle_unsat_result(f)
        if isinstance(res, ASM):
            return proofterm.ProofTerm.assume(self.fact_hol[res.t])
        elif isinstance(res, RealCombine):
            i, l1, l2 = res.i, self.handle_unsat_result(res.deriv1), self.handle_unsat_result(res.deriv2)
            c1, c2 = term_to_factoid(self.vars, l1.prop)[i], term_to_factoid(self.vars, l2.prop)[i]
            g = gcd(c1, c2)
            return self.real_combine_pt(l1, l2, int(c1/g), int(c2/g))
        
        elif isinstance(res, GCDCheck):
            return self.gcd_pt(self.vars, self.handle_unsat_result(res.deriv))
        
        elif isinstance(res, DirectContr):
            d1, d2 = extract(res.deriv1), extract(res.deriv2)

    def solve(self):
        res, value = solve_matrix(self.factoids)
        if res == "SAT":
            return value
        elif res == "UNSAT":
            pass
