"""
Implementation of Omega Test decision procedure.

Reference: https://github.com/HOL-Theorem-Prover/HOL/blob/develop/src/integer/OmegaMLShadow.sml
"""
import collections
import functools
from math import gcd, ceil, floor
from kernel.term import Int
import copy

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
                h += i * self.coeff[i]
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
    return a * b / (gcd(a, b))

def combine_real_factoid(i, f1, f2):
    """
    takes two factoids and produces a fresh one by "variable
    elimination" over the i'th variable in the vector.  It requires
    that the coefficient of v_i is strictly positive in f1, and
    strictly negative in f2.  The combination may produce a factoid where
    the coefficients can all be divided through by some number, but
    this factor won't be the gcd of the coefficients of v_i; this
    factor is eliminated from the outset.
    """
    assert f1[i] > 0 and f2[i] < 0, "combine_real_factoid"
    assert i < len(f1) - 1
    c0, d0 = f1[i], -f2[i]
    l = lcm(c0, d0)
    c, d = int(l / d0), int(l / c0)
    real_factoid = [c * n + d * m for m, n in zip(f1, f2)]
    return Factoid(real_factoid)

def combine_dark_factoid(i, f1, f2):
    """
    takes two factoids and combines them to produce a new, "dark shadow"
    factoid.  As above, the first one must have a positive coefficient of
    i, and the second a negative coefficient.
    """
    assert f1[i] > 0 and f2[i] < 0, "combine_dark_factoid"
    a, b = f1[i], -f2[i]
    dark_factoid = [a * n + b * m for m, n in zip(f1, f2)]
    dark_factoid[-1] = dark_factoid[-1] - (a - 1) * (b - 1)
    return Factoid(dark_factoid)


def factoid_gcd(f):
    """
    eliminates common factors in the variable coefficients of a factoid,
    or raises the exception no_gcd, if there is no common factor.
    """
    g = functools.reduce(gcd, f[:-1])
    if g < 1:
        raise NoGCDException

    elim_gcd_factoid = [floor(i / g) for i in f]
    return Factoid(elim_gcd_factoid)

def dest_plus(tm):
    """tm is of form x + y, return (x, y)"""
    if not tm.is_plus():
        return (tm,)
    if not tm.arg1.is_plus():
        return (tm.arg1, tm.arg)
    else:
        return dest_plus(tm.arg1) + (tm.arg,)

def dest_times(tm):
    """tm is of form x * y, return (x, y)"""
    assert tm.is_times()
    return (tm.arg1, tm.arg)


def term_to_factoid(vars, tm):
    """
    returns the factoid corresponding to tm.  tm is thus of the form
      0 <= c1 * v1 + ... + cn * vn + num
    Assumes that the variables are in the "correct" order (as given in the
    list vars), but that all are not necessarily present.  Omission
    indicates a coefficient of zero, of course.
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
                c, mv = dest_times(s)
                if mv == v:
                    return [c.dest_number()] + mk_coeff(vlist[1:], slist[1:])
                else:
                    return [0] + mk_coeff(vlist[1:], slist)
            else:
                return [0] + mk_coeff(vlist[1:], slist)

    return Factoid(mk_coeff(vars, dest_plus(tm)))

def factoid_to_term(vars, f):
    """
    returns the term corresponding to f, interpreting f over the list of
    variables vars.
    """
    t = None
    for v, c in zip(vars, f[:-1]):
        if c != 0:
            t += Int(c) * v
    
    return t + Int(f[-1])


class Derivation:
    """A derivation is a proof of a factoid."""
    pass

class ASM(Derivation):
    def __init__(self, t):
        self.t = t

    def __str__(self):
        return "ASM %s" % str(self.t)

    def __repr__(self):
        return str(self)

class RealCombine(Derivation):
    def __init__(self, i, deriv1, deriv2):
        self.i = i
        self.deriv1 = deriv1
        self.deriv2 = deriv2

    def __str__(self):
        return "REAL_COMBIN var %s: %s <*> %s" % (str(self.i), str(self.deriv1), str(self.deriv2))

    def __repr__(self):
        return str(self)

class GCDCheck(Derivation):
    def __init__(self, deriv):
        self.deriv = deriv

    def __str__(self):
        return "GCD_CHECK: %s" % str(self.deriv)

    def __repr__(self):
        return str(self)

class DirectContr(Derivation):
    def __init__(self, deriv1, deriv2):
        self.deriv1 = deriv1
        self.deriv2 = deriv2

    def __str__(self):
        return "DIRECT_CONTR: %s ~~ %s" % (str(self.deriv1), str(self.deriv2))

    def __repr__(self):
        return str(self)

dfactoid = collections.namedtuple('dfactoid', ['factoid', 'deriv'])

def split_dfactoid(df):
    return (df.factoid.key, df.factoid.constant, df.deriv)

class Result:
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

def direct_contradiction(d1, d2):
    return Contr(DirectContr(d1, d2))

def gcd_check_dfactoid(df):
    try:
        return (factoid_gcd(df.factoid), GCDCheck(df.deriv))
    except:
        return (df.factoid, df.deriv)

def dfactoid_key(f, d):
    return f.key

def dfactoid_derivation(f, d):
    return d

def term_to_dfactoid(vars, t):
    return (term_to_factoid(vars, t), ASM(t))


"""
    The "elimination mode" datatype.

    This records what sort of shadow we're currently working on.

"""

REAL, DARK, EXACT, EDARK = range(4)

"""
REAL when we're looking for a contradiction (only)
DARK when we're looking for satisfiability and the problem is not
     exact
EXACT when we're looking for either a contradiction or satisfiability.
EDARK when we're looking for satisfiability (i.e., have switched from
      a REAL search, but where the problem is still EXACT)
"""

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
    if em == DARK:
        return dfactoid(combine_dark_factoid(i, f1, f2), d1)
    else:
        return dfactoid(combine_real_factoid(i, f1, f2), RealCombine(i, d1, d2))

"""
The "db" datatype

So far, I'm using a Patricia tree to store my sets of constraints,
so the function parameters of type "database" are often called
ptree.  The keys are the hashes of the constraint keys.  The items
are lists (buckets) of dfactoids.

So far, we implemented a mutable mapping.
"""

class DataBase(collections.abc.MutableMapping):
    def __init__(self, *args, **kwargs):
        self.store = dict()
        self.update(dict(**kwargs))  # use the free update to set keys
        self.width = args[0]

    def __getitem__(self, key):
        return self.store[self.__keytransform__(key)]

    def __setitem__(self, key, value):
        self.store[self.__keytransform__(key)] = value

    def __delitem__(self, key):
        del self.store[self.__keytransform__(key)]

    def __iter__(self):
        return iter(self.store)

    def __len__(self):
        return len(self.store)

    def __keytransform__(self, key):
        return hash(key)
    
    def __str__(self):
        return str(self.store)

    def __repr__(self):
        return super().__repr__()

    def insert(self, *dfs):
        for df in dfs:
            f = df.factoid
            if hash(f) not in self.store.keys():
                self.store[self.__keytransform__(f)] = [df]
            else:
                self.store[self.__keytransform__(f)].append(df)

def lookup_fkey(db, fk):
    if hash(fk) in db.keys():
        alist = db[hash(fk)]
        for df in alist:
            if df.factoid.key == fk.key:
                return df
        raise KeyError
    else:
        raise KeyError

def dbadd(db, df):
    """
    dbadd df db

    Precondition: df is neither a trivially true nor false factoid.

    adds a dfactoid (i.e., a factoid along with its derivation) to a
    database of accumulating factoids.  If the factoid is
    actually redundant, because there is already a factoid with the
    same constraint key in the tree with a less or equal constant,
    then the exception RedundantAddition is raised.  Otherwise the
    return value is the new database.
    """
    f = df.factoid
    db = copy.deepcopy(db)
    if hash(f) in db.keys():
        for v in db[hash(f)]:
            if v.factoid.constant <= f.constant and v.factoid.key == f.key:
                raise RedundantAdditionException("Already have %s, so %s is redundant." % (str(v.factoid), str(df.factoid)))
        db[hash(f)].append(df)

    else:
        db[hash(f)] = [df]

    return db

def add_check_factoid(db0, df, next, kont):
    """
    When add a factoid A, if there is a factoid B in database, whose keys are
    opposite to keys in A. Suppose constant in A is ac, constant in B is bc, if
    bc < ~ac, then we can derive a diretct contradiction from A and B.
    """
    try:
        db = dbadd(db0, df)
    except RedundantAdditionException:
        return next(db0, kont)
    fk, fc = df.factoid.split_factoid()
    try:
        negdf = lookup_fkey(db, negate_key(df.factoid))
    except KeyError:
        return next(db, kont)

    negf, negd = negdf.factoid, negdf.deriv
    negc = negf.constant
    if negc < -fc:
        return kont(direct_contradiction(df.deriv, negd))
    else:
        return next(db, kont)
    
    

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
    def assign_factoid(df, upper, lower):
        fk, fc, d = split_dfactoid(df)
        if fk[x_var] < 0:
            if upper is None or upper[0] > fc:
                return ((fc, d), lower)
            else:
                return (upper, lower)
        else:
            if lower is None or lower[0] < -fc:
                return (upper, (-fc, d))
            else:
                return (upper, lower)

    for _, dfs in db.items():
        for df in dfs:
            f = df.factoid
            for index, k in enumerate(f.key):
                upper, lower = assign_factoid(df, upper, lower)

    if upper is None and lower is None:
        raise ValueError
    elif upper is not None and lower is None:
        if em == REAL:
            return NoConcl
        else:
            return Satisfiable(x_var = upper[0])
    elif upper is None and lower is not None:
        if em == REAL:
            return NoConcl
        else:
            return Satisfiable(x_var = lower[0])
    else:
        u, du, l, dl = upper[0], upper[1], lower[0], lower[1]
        if u < l:
            if em in (DARK, EDARK):
                return NoConcl
            else:
                return direct_contradiction(du, dl)
        else:
            if em == REAL:
                return NoConcl
            else:
                return Satisfiable({x_var:u})

def throwaway_redundant_factoids(db, nextstage, kont):
    """
    throwaway_redundant_factoids ptree nextstage kont

    checks ptree for variables that are constrained only in one sense
    (i.e., with upper or lower bounds only).

    The function nextstage takes a ptree and a continuation; it is
    called when ptree has run out of constraints that can be thrown
    away.

    The continuation function kont is of type result -> 'a, and will be
    called when the whole process eventually gets an answer.  This code
    will not call it directly, but if it does throw anything away, it will
    modify it so that a satisfying value can be calculated for the variables
    that are chucked.
    """
    dwidth = db.width
    numvars = db.width - 1
    has_low, has_up = [False] * numvars, [False] * numvars
    for _, dfactoids in db.items():
        for df in dfactoids:
            fk = df.factoid.key
            for i, k in enumerate(fk):
                if k < 0:
                    has_up[i] = True
                elif k > 0:
                    has_low[i] = True
    
    def find_redundant_var(db):
        for _, dfactoids in db.items():
            for df in dfactoids:
                fk = df.factoid.key
                for i, k in enumerate(fk):
                    if has_low[i] != has_up[i]:
                        return (i, has_up[i])
        return None

    if find_redundant_var(db) is not None:
        j, state = find_redundant_var(db)
        new_db = DataBase(db.width)
        elim = [] # store redundant factoids   
        for _, dfactoids in db.items():
            for df in dfactoids:
                fk = df.factoid.key
                if fk[j] == 0:
                    new_db.insert(df)
                else:
                    elim.append(df)
        def handle_result(r):
            if isinstance(r, Satisfiable):
                vmap = r.store
                def mapthis(df):
                    if has_up[j]:
                        v = floor(-df.factoid.eval_factoid_except(vmap, j)/df.factoid[j])
                    else:
                        v = ceil(-df.factoid.eval_factoid_except(vmap, j)/df.factoid[j])
                    return v
                evaluated = [mapthis(df) for df in elim]
                if has_up[j]:
                    r.update({j:min(evaluated)})
                else:
                    r.update({j:max(evaluated)})
                return r
            else:
                return r

        def kont_result(r):
            return kont(handle_result(r))
        return throwaway_redundant_factoids(new_db, nextstage, kont_result)
    else:
        return nextstage(db, kont)    

def exact_var(db):
    """
    An exact var is one that has coefficients of one in either all of its
    upper bounds or all of its lower bounds.  This function returns
    SOME v if v is an exact var in ptree, or NONE if there is no exact
    var.
    """
    up_coeffs_unit = [True] * (db.width - 1)
    low_coeffs_unit = [True] * (db.width - 1)
    coeffs_all_zero = [True] * (db.width - 1)

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

    for i in range(db.width - 1):
        if low_coeffs_unit[i] and not coeffs_all_zero[i]:
            return i
    for i in range(db.width - 1):
        if up_coeffs_unit[i] and not coeffs_all_zero[i]:
            return i

    return None

def least_coeff_var(db):
    """
    Returns the variable whose coefficients' absolute values sum to the
    least amount (that isn't zero).
    """
    sums = [0] * (db.width - 1)
    for _, dfactoids in db.items():
        for df in dfactoids:
            f = df.factoid
            for i, ai in enumerate(f.key):
                sums[i] += abs(ai)
    
    def find_min(lst):
        lst = sorted(lst)
        for index, el in enumerate(lst):
            if el != 0:
                return (index, el)


    return find_min(sums)

def generate_row(db0, em, i, up, lows, next, kont):
    """
    "Resolves" dfactoid against all the factoids in lows, producing new
    factoids, which get added to the ptree.  If a factoid is directly
    contradictory, then return it immediately, using kont.  If a factoid
    is vacuous, drop it.
    """

    def after_add(db, k):
        return generate_row(db, em, i, up, lows[1:], next, k)

    if lows == []:
        return next(db0, kont)
    else:
        low = lows[0]
        f, d = gcd_check_dfactoid(combine_dfactoid(em, i, low.factoid, low.deriv, up.factoid, up.deriv))
        if f.is_true_factoid():
            return generate_row(db0, em, i, up, lows[1:], next, kont)
        elif f.is_false_factoid():
            return kont(Contr(d))
        else:
            return add_check_factoid(db0, dfactoid(f, d), after_add, kont)

def generate_cross_product(db0, em, i, ups, lows, next, kont):
    """
    Operate generate_row on each up in ups.
    """
    if ups == []:
        return next(db0, kont)
    else:
        u = ups[0]
        def after(db, k):
            return generate_cross_product(db, em, i, ups[1:], lows, next, k)
        return generate_row(db0, em, i, u, lows, after, kont)

def extend_vmap(db, i, vmap):
    """
    vmap provides values for all of the variables present in ptree's
    factoids except i.  Use it to evaluate all of the factoids, except
    at variable i and to then return vmap extended with a value for
    variable i that respects all of the factoids.
    """
    def categorise(df, lower, upper):
        f = df.factoid
        c0 = f.eval_factoid_except(vmap, i)
        fk = f.key
        coeff = fk[i]

        if coeff < 0: #upper case
            c = floor(c0/(-coeff))
            if upper is None or c < upper:
                return (lower, c)
            else:
                return (lower, upper)

        elif coeff == 0:
            return (lower, upper)
        
        else: #lower case
            c = ceil(-(c0/(coeff)))
            if lower is None or c > lower:
                return (c, upper)
            else:
                return (lower, upper)

    lower, upper = None, None

    for _, dfactoids in db.items():
        for df in dfactoids:
            lower, upper = categorise(df, lower, upper)
    
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

def one_step(db, em, next, kont):
    """
    Assume that ptree doesn't contain anything directly contradictory,
    and that there aren't any redundant constraints around (these have
    been thrown away by throwaway_redundant_factoids).

    Perform one step of the shadow calculation algorithm:
      (a) if there is only one variable left in all of the constraints
          in ptree do one_var_analysis to return some sort of result,
          and pass this result to kont.
      (b) otherwise, decide on a variable to eliminate.  If there's a
          variable that allows for an exact shadow (has coefficients of
          one in all of its lower-bound or upper-bound occurrences),
          pick this.  Otherwise, take the variable whose coefficients'
          absolute values sum to the least amount.
      (c) the initial tree of the result contains all of those
          constraints from the original which do not mention the
          variable to be eliminated.
      (d) divide the constraints that do mention the variable to be
          eliminated into upper and lower bound sets.
    Then (in generate_crossproduct):
      (e) work through all of the possible combinations in
            upper x lower
          using combine_dfactoids.  Each new dfactoid has to be added
          to the accumulating tree.  This may produce a direct
          contradiction, in which case, stop and return this (again,
          using the kont function).  Otherwise keep going.
      (f) pass the completed new ptree to nextstage, with an augmented
          continuation that copes with satisfiable results (though
          satisfiable results won't come back if the mode is REAL
          of course).
    """
    var_to_elim, mode = exact_var(db), em
    if var_to_elim is None:
        var_to_elim, _ = least_coeff_var(db)
        mode = inexactify(em)

    def categorise(df, notmentioned, uppers, lowers):
        f = df.factoid
        if f[var_to_elim] < 0:
            return (notmentioned, [df] + uppers, lowers)
        elif f[var_to_elim] == 0:
            notmentioned.insert(df)
            return (notmentioned, uppers, lowers)
        else:
            return (notmentioned, uppers, [df] + lowers)
    lowers, uppers = [], []
    newdb = DataBase(db.width)
    for _, dfactoids in db.items():
        for df in dfactoids:
            newdb, uppers, lowers = categorise(df, newdb, uppers, lowers)

    def drop_contr(re):
        return NoConcl if isinstance(re, Contr) else re

    def extend_satisfiable(r):
        if isinstance(r, Satisfiable):
            return Satisfiable(extend_vmap(db, var_to_elim, r.store))
        else:
            return r
    def newkont(em, mode):
        def _newkont(r):
            if em == EXACT and mode == EXACT:
                return extend_satisfiable(r)
            elif em == EXACT and mode == REAL:
                if isinstance(r, Contr):
                    return r
                else:
                    return one_step(db, EDARK, next, kont)
            elif em == REAL and mode == REAL:
                return r
            elif em == EDARK and mode == EDARK:
                return drop_contr(extend_satisfiable(r))
            elif em == EDARK and mode == DARK:
                return drop_contr(extend_satisfiable(r))
            elif em == DARK and mode == DARK:
                return drop_contr(extend_satisfiable(r))
            else:
                raise ValueError
        return _newkont

    def newnext(db, k):
        return next(db, mode, k)

    return generate_cross_product(newdb, em, var_to_elim, uppers, lowers, newnext, newkont(em, mode))

def kont(r):
    return r

def toplevel(db, em, kont):
    def after_throwaway(db, k):
        if len(db) == 0:
            return k(Satisfiable(zero_upto(db.width - 2)))
        elif has_one_var(db):
            return k(mode_result(em, one_var_analysis(db, em)))
        else:
            return k(one_step(db, em, toplevel, k))

    return throwaway_redundant_factoids(db, after_throwaway, kont)

def solve_matrix(matrix, mode=EXACT):
    """
    Give some factoids, return the result.
    """
    fs = [Factoid(f) for f in matrix]
    db = DataBase(len(matrix[0]))
    db.insert(*[dfactoid(ft, ASM(ft)) for ft in fs])
    return toplevel(db, DARK, kont).store
