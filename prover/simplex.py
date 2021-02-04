"""
Note that the equality dict in Simplex data structure can be simplified by elimate the jar whose coefficient
is zero. This will be fixed later.
"""

"""
Implementation of Simplex-based quantifier-free linear arithmetic solver.

Reference: 
Bruno Dutertre and Leonardo de Moura. A Fast Linear-Arithmetic Solver for DPLL(T) 
"""

from kernel.term import Term, Var, Inst, Int, greater_eq, Real, Eq, less_eq, minus, greater, less, Const, TFun, of_int
from kernel.type import RealType, IntType
from kernel.proofterm import ProofTerm
from kernel.theory import register_macro, Thm, get_theorem
from kernel.macro import Macro
from logic.logic import apply_theorem
from logic import basic, matcher
from data import real, integer
from logic.conv import Conv, ConvException, rewr_conv, top_conv, arg_conv, arg1_conv, bottom_conv
from collections import namedtuple
from collections import deque
import math
import numbers
import string
from fractions import Fraction
import functools
import hashlib

basic.load_theory('real')

SAT, UNSAT = range(2)

geq_atom = namedtuple("geq_atom", ["var_name", "lower"])
leq_atom = namedtuple("leq_atom", ["var_name", "upper"])


class AssertUpperException(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class UNSATException(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class AssertLowerException(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class Jar:
    """A pair (coeff, name), represent a coeff * var term."""
    def __init__(self, coeff, var):
        assert(isinstance(coeff, numbers.Number))
        assert(isinstance(var, str))
        self.coeff = coeff
        self.var = var

    def __str__(self):
        return "%s * %s" % (str(self.coeff), self.var)

    def __repr__(self):
        return "Jar(%s, %s)" % (str(self.coeff), self.var)

    def __hash__(self):
        return int(hashlib.sha1(self.var.encode('utf-8')).hexdigest(), 16) % (10 ** 8) + self.coeff ** 3

    def __eq__(self, value):
        return type(value) == Jar and self.coeff == value.coeff and self.var == value.var


class Bound:
    def __init__(self, lower, upper):
        assert isinstance(lower, numbers.Number) and isinstance(upper, numbers.Number)
        self.lower = lower
        self.upper = upper

    def __str__(self):
        return "[%s, %s]" % (str(self.lower), str(self.upper))

class Equation:
    """Each equation contains a dependent variable, and several independent variables."""
    def __init__(self, dept, indepts):
        assert isinstance(dept, Jar)
        assert all(isinstance(idt, Jar) for idt in indepts)
        self.dept = dept
        self.indepts = indepts

class InEquation:
    pass

class GreaterEq(InEquation):
    """Represent a greater equality term."""
    def __init__(self, jars, lower_bound):
        assert(all(isinstance(j, Jar) for j in jars))
        assert(isinstance(lower_bound, numbers.Number))
        self.jars = tuple(jars)
        self.lower_bound = lower_bound

    def __str__(self):
        return " + ".join([str(jar) for jar in self.jars]) + " >= " + str(self.lower_bound)
        


class LessEq(InEquation):
    """Represent a greater equality term."""
    def __init__(self, jars, upper_bound):
        assert(all(isinstance(j, Jar) for j in jars))
        assert(isinstance(upper_bound, numbers.Number))
        self.jars = tuple(jars)
        self.upper_bound = upper_bound

    def __str__(self):
        return " + ".join([str(jar) for jar in self.jars]) + " <= " + str(self.upper_bound)

class Tableau:
    """A tableau is a list of equalities.
    """
    def __init__(self, eqs):
        assert all(isinstance(eq, Equation) for eq in eqs)
        self.eqs = eqs

    def __len__(self):
        return len(self.eqs)

    def __getitem__(self, pos):
        return self.eqs[pos]

def collect_vars_from_ineq(ineq):
    """Give an inequation, return a set in which are the _vars."""
    assert isinstance(ineq, InEquation)
    _vars = set()
    for jar in ineq.jars:
        _vars.add(jar.var)

    return _vars

def find_coeff(v, jars):
    """Give a list of jars, return the jar whose variable is v,
    otherwise, return None
    """
    for i, j in enumerate(jars):
        if j.var == v:
            return (i, j)
    
    return (None, None)
    
def reduce_pairs(ps):
    """
    Same as the implementation in integral.poly. Reduce a list of pairs bycollecting 
    into groups according to first components, and adding the second component for each group.

    e.g. [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]
    """
    res = {}
    for p in ps:
        v, c = p.var, p.coeff
        if v in res:
            res[v] += c
        else:
            res[v] = c
    
    pair = tuple(sorted((k, v) for k, v in res.items()))
    jars = [Jar(v, k) for k, v in pair]
    return jars

def delete_key(d, key):
    """delete a item in dict"""
    r = dict(d)
    del r[key]
    return r

def delete_elem(s, elem):
    """delete a item in set"""
    r = set(s)
    r.remove(elem)
    return r

class Simplex:
    """"""
    def __init__(self, ilp=False):
        # table represents the solver current tableau(state)
        self.equality = dict()

        # elementary atoms: y ⋈ b
        self.lower_atom = [] # y >= b
        self.upper_atom = [] # y <= b
        self.atom = []
        
        # mapping is the assignment for each variable
        self.mapping =  dict()
        
        # basic are the basic variables
        self.basic = set()
        
        # non_baic are the non-basic variables
        self.non_basic = set()
        
        # index for new introduced variable
        self.index = 0
        
        # bounds is a dict, key is the var_name, value is a pair: (lower_bound, upper_bound)
        self.bound = dict()

        # key is non-basic variable, value are the basic variables corresponding to it
        self.nbasic_basic = dict()

        # orignial inequalities inserted into solver
        self.original = []

        # basic variable that can't find a suitable value
        self.wrong_var = None

        # Restore the pivot trace: ((xi, xj), aij, nbasic[xj]) each time call check()
        self.trace = []

        # input vars
        self.input_vars = set()

        # represents whether this is an ILP problem
        self.ilp = ilp

        # represents the input non-atom expressions
        self.matrix = dict()

    def __str__(self):
        s = "Original inequlities: \n"
        for ineq in self.original:
            s += "\t %s\n" % str(ineq) 

        s += "Equality:\n"
        for lhs, rhs in self.equality.items():
            s += "\t %s := " % str(lhs) + " + ".join(str(jar) for jar in rhs) + "\n"

        s += "\nlower_atom:\n"
        for lhs, rhs in self.lower_atom:
            s += "\t %s >= %s\n" % (str(lhs), str(rhs))

        s += "\nupper_atom:\n"
        for lhs, rhs in self.upper_atom:
            s += "\t %s <= %s\n" % (str(lhs), str(rhs))

        s += "\nAssignments:\n"

        for key, value in self.mapping.items():
            s += "\t %s := %s\n" % (str(key), str(value))

        s += "\nBasic Variables:\n"
        for b in self.basic:
            s += "\t" + b + "\n"

        s += "\nNon-basic Variables:\n"
        for b in self.non_basic:
            s += "\t" + b + "\n"

        s += "\nBounds:\n"
        for key, (lower, upper) in self.bound.items():
            s += "\t %s: [%s, %s]\n" % (key, str(lower), str(upper))

        s += "\nRelation between non-basic variables and corresponding basic variables\n"
        for key, value in self.nbasic_basic.items():
            s += "\t %s: " % str(key) + ", ".join(str(v) for v in value) + "\n"
        return s

    def add_ineq(self, ineq):
        """
        Add an inequality to the current solver, and update relevant states.
        """
        assert isinstance(ineq, InEquation)
        self.original.append(ineq)
        if isinstance(ineq, GreaterEq):
            if len(ineq.jars) == 1: # a * x >= b
                jar = ineq.jars[0]
                coeff, var_name, lower_bound = jar.coeff, jar.var, ineq.lower_bound
                self.input_vars.add(var_name)
                if coeff == 1: # x >= b (atom)
                    self.lower_atom.append((var_name, lower_bound))
                    self.atom.append(geq_atom(var_name, lower_bound))
                    if var_name not in self.mapping:
                        self.mapping[var_name] = 0
                    self.non_basic.add(var_name)
                    if var_name not in self.bound.keys():
                        self.bound[var_name] = (-math.inf, math.inf)
            

                elif coeff != 0: # a * x >= b
                    if ineq.jars not in self.matrix:
                        s = "$" + string.ascii_lowercase[self.index] + "$"
                        self.index += 1
                        self.matrix[ineq.jars] = s
                        self.equality[s] = ineq.jars
                    else:
                        s = self.matrix[ineq.jars]
                    self.lower_atom.append((s, lower_bound))
                    self.atom.append(geq_atom(s, lower_bound))
                    self.basic.add(s)
                    self.non_basic.add(var_name)
                    if var_name not in self.nbasic_basic:
                        self.nbasic_basic[var_name] = {s}
                    else:
                        self.nbasic_basic[var_name].add(s)        
            
                    if var_name not in self.mapping:
                        self.mapping.update({var_name : 0, s : 0})
                    self.bound[s] = (-math.inf, math.inf)
                    if var_name not in self.bound:
                        self.bound[var_name] = (-math.inf, math.inf)

            else: # a * x + b * y + ... >= c
                _vars = collect_vars_from_ineq(ineq)
                # push all variables in lhs into solver
                for v in _vars:
                    if v not in self.mapping.keys():
                        self.mapping.update({v: 0})
                    if v not in self.non_basic:
                        self.non_basic.add(v)
                    if v not in self.bound.keys():
                        self.bound[v] = (-math.inf, math.inf)
                    self.input_vars.add(v) 

                lower_bound = ineq.lower_bound
                if ineq.jars not in self.matrix:
                    s = "$" + string.ascii_lowercase[self.index] + "$"
                    self.index += 1
                    self.equality[s] = ineq.jars
                    self.matrix[ineq.jars] = s
                else:
                    s = self.matrix[ineq.jars]
                self.lower_atom.append((s, lower_bound))
                self.atom.append(geq_atom(s, lower_bound))
                self.mapping[s] = 0
                for jar in ineq.jars:
                    if jar.var not in self.nbasic_basic:
                        self.nbasic_basic[jar.var] = {s}
                    else:
                        self.nbasic_basic[jar.var].add(s)
                
                self.basic.add(s)
                self.bound[s] = (-math.inf, math.inf)

        elif isinstance(ineq, LessEq):
            if len(ineq.jars) == 1: # a * x <= b
                jar = ineq.jars[0]
                coeff, var_name, upper_bound = jar.coeff, jar.var, ineq.upper_bound
                self.input_vars.add(var_name)
                if coeff == 1: # x <= b (atom)
                    self.upper_atom.append((var_name, upper_bound))
                    self.atom.append(leq_atom(var_name, upper_bound))
                    if var_name not in self.mapping:
                        self.mapping[var_name] = 0
                    self.non_basic.add(var_name)
                    if var_name not in self.bound.keys():
                        self.bound[var_name] = (-math.inf, math.inf)

                elif coeff != 0: # a * x <= b
                    if ineq.jars not in self.matrix:
                        s = "$" + string.ascii_lowercase[self.index] + "$"
                        self.index += 1
                        self.equality[s] = ineq.jars
                        self.matrix[ineq.jars] = s
                    else:
                        s = self.matrix[ineq.jars]
                    self.upper_atom.append((s, upper_bound))
                    self.atom.append(leq_atom(s, upper_bound))
                    
                    self.basic.add(s)
                    self.non_basic.add(var_name)
                    if var_name not in self.mapping:
                        self.mapping.update({var_name : 0, s : 0})
                    self.bound[s] = (-math.inf, math.inf)
                    if var_name not in self.nbasic_basic:
                        self.nbasic_basic[var_name] = {s}
                    else:
                        self.nbasic_basic[var_name].add(s)
                    if var_name not in self.bound.keys():
                        self.bound[var_name] = (-math.inf, math.inf)

            else: # a * x + b * y + ... <= c
                _vars = collect_vars_from_ineq(ineq)
                # push all variables in lhs into solver
                for v in _vars:
                    if v not in self.mapping.keys():
                        self.mapping.update({v: 0})
                    if v not in self.non_basic:
                        self.non_basic.add(v)
                    if v not in self.bound.keys():
                        self.bound[v] = (-math.inf, math.inf)
                    self.input_vars.add(v)

                upper_bound = ineq.upper_bound
                if ineq.jars not in self.matrix:
                    s = "$" + string.ascii_lowercase[self.index] + "$"
                    self.index += 1
                    self.equality[s] = ineq.jars
                    self.matrix[ineq.jars] = s
                else:
                    s = self.matrix[ineq.jars]
                self.upper_atom.append((s, upper_bound))
                self.atom.append(leq_atom(s, upper_bound))
                self.mapping[s] = 0
                for jar in ineq.jars:
                    if jar.var not in self.nbasic_basic:
                        self.nbasic_basic[jar.var] = {s}
                    else:
                        self.nbasic_basic[jar.var].add(s)

                self.basic.add(s)
                self.bound[s] = (-math.inf, math.inf)

        # if self.ilp:
        #     self.variables_bound()

    def __len__(self):
        return len(self.original)

    def preprocess(self):
        """
        Simplify the constraints Ax = 0 by Gauss elimination.
        Remove any variable xi that does not occur in any elementary atom of inequalities.
        Introduce a new variable when elimination is done.
        """
        pass

    def aij(self, xi, xj):
        """
        xi is a basic variable, xj is a non_basic variable.
        return the aij in the equation of xi = ... + aij * xj + ...
        """
        assert xi in self.basic and xj in self.non_basic
        jars = self.equality[xi]
        _, res =  find_coeff(xj, jars)
        return res.coeff if res is not None else 0
    
    def update(self, x, v):
        assert x in self.non_basic
        if x in self.nbasic_basic:
            rlt = self.nbasic_basic[x]
            for b in rlt:
                a = self.aij(b, x)
                self.mapping[b] += a * (v - self.mapping[x])
            
        self.mapping[x] = v

    def pivot(self, xi, xj):
        """
        xi is a basic variable, xj is a non-basic variable.
        Delete xi from basic sets, delete xj from non-basic sets
        Suppose the original equality is:
                        xi = ... + aij * xj + ...
        then we could the representation of xj:
                        xj = 1/aij * xi + -...
        After get the representation, we find other equalities which use xj,
        substitute xj with the above equality's rhs and normalize it.
        """
        assert xi in self.basic and xj in self.non_basic
        a = self.aij(xi, xj)
        # get the equality
        jars = self.equality[xi]
        xj_repr_jars = [Jar(Fraction(1, a), xi)] + [Jar(-Fraction(1, a) * Fraction(jar.coeff), jar.var) for jar in jars if jar.var != xj]
        xj_repr_jars = reduce_pairs(xj_repr_jars)
        # update the state
        
        # update equality, delete the previous xi = ...
        # add new term xj = ... 
        # for the other equalities which use xj, try to substitute xj
        # by xj_repr_jars
        self.equality = delete_key(self.equality, xi)
        self.equality[xj] = xj_repr_jars

        for x in self.nbasic_basic[xj]:
            if x != xi:
                rhs = self.equality[x]
                _, xj_jar = find_coeff(xj, rhs)
                rhs_without_xj = reduce_pairs([j for j in rhs if j != xj_jar] + [Jar(xj_jar.coeff * v.coeff, v.var) for v in xj_repr_jars])
                self.equality[x] = rhs_without_xj

        # update basic and non_basic variables
        self.basic = delete_elem(self.basic, xi)
        self.non_basic = delete_elem(self.non_basic, xj)
        self.basic.add(xj)
        self.non_basic.add(xi)

        # update nbasic_basic
        self.nbasic_basic = dict()
        for key, value in self.equality.items():
            for v in value:
                if v.var in self.nbasic_basic:
                    self.nbasic_basic[v.var].add(key)
                else:
                    self.nbasic_basic[v.var] = {key}

    def pivotAndUpdate(self, xi, xj, v):
        assert xi in self.basic and xj in self.non_basic
        a = self.aij(xi, xj)
        theta = Fraction(v - self.mapping[xi], a)
        self.mapping[xi] = v
        self.mapping[xj] = self.mapping[xj] + theta
        for xk in self.basic:
            if xk != xi:
                k = self.aij(xk, xj)
                self.mapping[xk] += k * theta

        self.pivot(xi, xj)

    def assert_upper(self, x, c):
        assert x in self.bound, "No such variable in solver"
        l, u = self.bound[x]
        
        if c < l:
            raise AssertUpperException("%s's lower bound %s is larger than %s" % (x, str(l), str(c)))
        elif c < u:
            self.bound[x] = (l, c)
            if x in self.non_basic and self.mapping[x] > c:
                self.update(x, c)

    def assert_lower(self, x, c):
        assert x in self.bound, "No such variable in solver"
        l, u = self.bound[x]
        if c > u:
            raise AssertLowerException("%s's lower bound %s is larger than %s" % (x, str(l), str(c)))
        elif c > l:
            self.bound[x] = (c, u)
            if x in self.non_basic and self.mapping[x] < c:
                self.update(x, c)

    def check(self):
        self.wrong_var = None
        self.pivot_trace = []
        while True:
            basic_vars = sorted(list(self.basic))
            flag = False
            for v in basic_vars:
                if self.bound[v][0] > self.mapping[v] or self.bound[v][1] < self.mapping[v]:
                    xi = v
                    flag = True
            if not flag:
                return SAT
            
            if self.mapping[xi] < self.bound[xi][0]:
                flag = False
                rhs_jars = reduce_pairs(self.equality[xi])
                for j in rhs_jars:
                    coeff, xj = j.coeff, j.var
                    if coeff > 0 and self.mapping[xj] < self.bound[xj][1] or\
                        coeff < 0 and self.mapping[xj] > self.bound[xj][0]:
                        self.trace.append(((xi, xj), coeff, self.nbasic_basic[xj]))
                        self.pivotAndUpdate(xi, xj, self.bound[xi][0])
                        flag = True
                        break
                if not flag:
                    self.wrong_var = xi
                    return UNSAT

            if self.mapping[xi] > self.bound[xi][1]:
                flag = False
                rhs_jars = reduce_pairs(self.equality[xi])
                for j in rhs_jars:
                    coeff, xj = j.coeff, j.var
                    if coeff < 0 and self.mapping[xj] < self.bound[xj][1] or\
                        coeff > 0 and self.mapping[xj] > self.bound[xj][0]:
                        self.trace.append(((xi, xj), coeff, self.nbasic_basic[xj]))
                        self.pivotAndUpdate(xi, xj, self.bound[xi][1])
                        flag = True
                        break
                
                if not flag:
                    self.wrong_var = xi
                    return UNSAT

    def handle_assertion(self):
        for assertion in self.atom:
            if isinstance(assertion, leq_atom):
                self.assert_upper(assertion.var_name, assertion.upper)
                
            else:
                self.assert_lower(assertion.var_name, assertion.lower)

            # if assertion.var_name in self.basic:
            res = self.check()
            if res == UNSAT:
                raise UNSATException("variable %s is wrong." % str(self.wrong_var))

    def explaination(self, xi):
        """
        When a conflict occurs, return the minimal clause.

        There are two main reasons for inconsistency:

        1) A basic variable xi such that β(xi) < li and for all non-basic variable we have
        aij > 0 --> β(xj) ≥ uj and aij < 0 --> β(xj) ≤ lj.

        2) A basic variable xj such that β(xj) > uj and for all non-basic variable we have
        aij > 0 --> β(xj) ≤ lj and aij < 0 --> β(xj) ≥ uj.

        For 1), the clause is
            Γ  = {xj ≤ uj | j ∈ N+} ∪ {xj ≥ lj | j ∈ N-} ∪ {xi ≥ li}

        For 2), the clause is
            Γ  = {xj ≥ lj | j ∈ N+} ∪ {xj ≤ uj | j ∈ N-} ∪ {xj ≤ ui}
        """
        explain = [] # store the atoms
        if self.mapping[xi] < self.bound[xi][0]: # reason 1
            for jar in self.equality[xi]:
                if jar.coeff > 0:
                    upper = self.bound[jar.var][1]
                    explain.append(leq_atom(jar.var, upper))
                elif jar.coeff < 0:
                    lower = self.bound[jar.var][0]
                    explain.append(geq_atom(jar.var, lower))
            explain.append(geq_atom(xi, self.bound[xi][0]))

        else:
            for jar in self.equality[xi]:
                if jar.coeff > 0:
                    lower = self.bound[jar.var][0]
                    explain.append(geq_atom(jar.var, lower))
                elif jar.coeff < 0:
                    upper = self.bound[jar.var][1]
                    explain.append(leq_atom(jar.var, upper))
            explain.append(leq_atom(xi, self.bound[xi][1]))    

        return explain

    def theta(self):
        """
        For Ax ≤ b, Ax ≥ c. 
            θ(A) = max(|aij|), θ(b) = max(|bi|), θ(c) = max(|ci|)
        θ is max(θ(A), θ(b), θ(c))
        θ can be used to derive non-basic variables' bound.
        """
        t = 0
        ineqs = self.original
        for ineq in ineqs:
            if isinstance(ineq, GreaterEq):
                jars, lower_bound = ineq.jars, ineq.lower_bound
                for j in jars:
                    if abs(j.coeff) > t:
                        t = abs(j.coeff)
                if abs(lower_bound) > t:
                    t = abs(lower_bound)
            else:
                jars, upper_bound = ineq.jars, ineq.upper_bound
                for j in jars:
                    if abs(j.coeff) > t:
                        t = abs(j.coeff)
                if abs(upper_bound) > t:
                    t = abs(upper_bound)
        return t

    def variables_bound(self):
        """
        Compute each non-basic variables' bound based on the following theorem(NEMHAUSER, 1998, P125):
        If x is an extreme point of conv(S), then:
                x <= ((m+n)nθ)^n
        Where m is the number of inequations, n is the number of non-basic vars.
        """
        m = len(self.original)
        n = len(self.basic)
        t = self.theta()
        bound = ((m + n) * n * t) ** n

        # set the bound for each non-basic variable
        for var in self.non_basic:
                if self.bound[var][0] < -bound:
                    self.bound[var] = (-bound, self.bound[var][1])
                if bound < self.bound[var][1]:
                    self.bound[var] = (self.bound[var][0], bound)

    def add_ineqs(self, *ineqs):
        for ineq in ineqs:
            self.add_ineq(ineq)

    def all_integer(self):
        """Check if all items in d are integer"""
        for var, value in self.mapping.items():
            if var in self.input_vars:
                v = float(value)
                if not v.is_integer():
                    return False
        return True

    def find_not_int_var(self):
        """Find the var which value is not integer."""
        assert not self.all_integer(), "No integer!"
        for v, value in self.mapping.items():
            if v in self.input_vars:
                val = float(value)
                if not val.is_integer():
                    return v, val
        return None

# def branch_and_bound(tableau):
#     """
#     If current solution is not a good solution(some variables' value are not integer),
#     add more constraints and perform simplex again, until find a good solution.
#     """
#     tree = deque([tableau])
#     while len(tree) != 0:
#         try:
#             simplex = tree.popleft()
#             simplex.handle_assertion()
#             if not simplex.all_integer():
#                 v, val = simplex.find_not_int_var()
#                 s1, s2 = Simplex(), Simplex()
#                 ineq1 = LessEq([Jar(1, v)], math.floor(val))
#                 ineq2 = GreaterEq([Jar(1, v)], math.ceil(val))
#                 s1.add_ineqs(ineq1, *simplex.original)
#                 s2.add_ineqs(ineq2, *simplex.original)
#                 tree.appendleft(s1)
#                 tree.appendleft(s2)
#             else:
#                 return simplex.mapping
                
                
#         except:
#             continue
    
#     print("No integer solution!")


def branch_and_bound(tableau):
    """
    If current solution is not a good solution(some variables' value are not integer),
    add more constraints and perform simplex again, until find a good solution.
    """
    T = IntSimplexTree(tableau)
    tree = deque([T])
    while len(tree) != 0:
        try:
            node = tree.popleft()
            node.simplex.handle_assertion()
            if not node.simplex.all_integer():
                v, val = node.simplex.find_not_int_var()
                node.var = v
                s1, s2 = Simplex(), Simplex()
                ineq1 = LessEq([Jar(1, v)], math.floor(val))
                ineq2 = GreaterEq([Jar(1, v)], math.ceil(val))
                s1.add_ineqs(ineq1, *node.simplex.original)
                s2.add_ineqs(ineq2, *node.simplex.original)
                b1, b2 = IntSimplexTree(s1, new_ast=ineq1), IntSimplexTree(s2, new_ast=ineq2)
                node.branches = (b1, b2)
                tree.appendleft(b1)
                tree.appendleft(b2)
            else:
                return node.simplex.mapping
                
                
        except:
            continue
    
    print("No integer solution!")
    return T


class IntSimplexTree:
    """The tree of branch and bound method."""
    def __init__(self, simplex, var=None, branches=(), new_ast=None):
        # var is the varible which splits the simplex
        self.var = var

        # simplex is the problem at this node
        self.simplex = simplex

        # branches are the subproblems, when simplex is UNSAT,
        # branches would be empty
        self.branches = branches

        # new_ast are the newly added assertions for the non-integer var
        self.new_ast = new_ast

    def __str__(self):
        s  = str(self.new_ast)
        for b in self.branches:
            s += "\n\t" + str(b)
        return s + "\n"

    def __repr__(self):
        s = " ".join(str(p) for p in self.simplex.original)
        for b in self.branches:
            s += "\n\t%s" % str(b)
        return s + "\n"


    def branch_and_bound_pt(self):
        """Get an unsat proof term for self.simplex."""
        if not self.branches:
            solver = SimplexHOLWrapper()
            solver.add_ineqs(self.simplex.original)
            pt_real = solver.handle_assertion()
            pt_integer = unsat_integer_simplex_stage2(solve_hol_integer_ineqs(pt_real))
            if self.new_ast is None:
                return pt_integer
            pt_integer1 = pt_integer.implies_intr(pt_integer.hyps[0])
            bound = pt_integer.hyps[0].arg
            bound_value = of_int(RealType)(Int(real.real_eval(bound)))
            value_pt = real.real_eval_conv().get_proof_term(bound_value)
            pt_integer2 = pt_integer1.on_prop(top_conv(replace_conv(value_pt.symmetric())))
            assert isinstance(pt_integer2, ProofTerm)
            if pt_integer.hyps[0].is_less_eq():
                return pt_integer2.on_prop(arg1_conv(rewr_conv('real_of_int_leq')))
            else:
                return pt_integer2.on_prop(arg1_conv(rewr_conv('real_of_int_geq')))
        else:
            pt1, pt2 = [b.branch_and_bound_pt() for b in self.branches]
            # pt1_intr_new_ast = pt1.implies_intr(ineq_to_term(self.branches[0].new_ast))
            # pt2_intr_new_ast = pt2.implies_intr(ineq_to_term(self.branches[1].new_ast))
            th = ProofTerm.theorem('int_geq_leq_true')
            inst = matcher.first_order_match(th.lhs.arg1, pt1.prop)
            pt_concl = th.substitution(inst).on_lhs(bottom_conv(integer.int_eval_conv()))
            pt_conj = apply_theorem('conjI', pt1, pt2)
            return pt_concl.equal_elim(pt_conj)

def dest_plus(tm):
    """tm is of form x + y, return (x, y)"""
    if not tm.is_plus():
        return (tm,)
    if not tm.arg1.is_plus():
        return (tm.arg1, tm.arg)
    else:
        return dest_plus(tm.arg1) + (tm.arg,)

def add_atom(d, key, atom):
    """
    d is a dict, add an atom to list d[key] 
    """
    if key not in d:
        d[key] = (atom, )
    else:
        d[key] = tuple(d[key] + (atom, ))
    
    return d  

def is_ineq(tm):
    """check if tm is an ineq term."""
    return tm.is_greater() or tm.is_greater_eq() or tm.is_less() or tm.is_less_eq()

def ineq_to_term(ineq):
    """Given an inequation, convert it to a hol term."""
    assert isinstance(ineq, InEquation)
    lhs_atoms = [Int(j.coeff) * Var(j.var, IntType) if j.coeff != 1 else Var(j.var, IntType) for j in ineq.jars]
    lhs = sum(lhs_atoms[1:], lhs_atoms[0])
    if isinstance(ineq, GreaterEq): # a * x + b * y + ... ≥ c    
        rhs = Int(ineq.lower_bound)
        return greater_eq(RealType)(lhs, rhs)
    else: # a * x + b * y + ... ≤ c
        rhs = Real(ineq.upper_bound)
        return less_eq(RealType)(lhs, rhs)

class replace_conv(Conv):
    def __init__(self, pt):
        self.pt = pt

    def get_proof_term(self, t):
        if t == self.pt.prop.lhs:
            return self.pt
        else:
            raise ConvException

class SimplexHOLWrapper:
    """
    Wrapper for simplex method in higher-order logic. 
    """
    def __init__(self, ilp=False):
        # core data structure
        self.simplex = Simplex()
        
        # proofterms for input inequlities, key is the HOL lhs
        self.ineq_pts = dict()

        # proofterms for equalities, key is the new introduced variable
        self.eq_pts = dict()

        # proofterm for atom inequalities, used in assertion procedure
        self.atom_ineq_pts = dict()

        # proofterms for bounds, key is variable.
        self.lower_bound_pts = dict()
        self.upper_bound_pts = dict()

        # additional equalities for introduced variables
        self.intro_eq = set()

        # Unsatisfiable proof, key is variable which leads to inconsistency
        self.unsat = dict()

    def __str__(self):
        s = "Inequality ProofTerms: \n"
        for _, pt in self.ineq_pts.items():
            s += "\t %s \n" % str(pt)
        
        s += "\nEquality ProofTerms: \n"
        for _, pt in self.eq_pts.items():
            s += "\t %s \n" % str(pt)
        
        s +="\nInequality atom ProofTerms:\n"
        for _, pt in self.atom_ineq_pts.items():
            s += "\t %s \n" % str(pt)

        s += "\nLower Bound ProofTerms:\n"
        for _, pt in self.lower_bound_pts.items():
            s += "\t %s \n" % str(pt)

        s += "\nUpper Bound ProofTerms:\n"
        for _, pt in self.upper_bound_pts.items():
            s += "\t %s \n" % str(pt)

        return s

    def add_ineq(self, ineq):
        """
        Take an inequation, convert it into higher-order logic terms.
        Add the inequation to ineq_pts.
        If necessary, introduce new variables to construct elemenatry atoms, and also
        add equality proofterm to eq_pts.
        """
        assert isinstance(ineq, InEquation)
        lhs_atoms = [Real(j.coeff) * Var(j.var, RealType) for j in ineq.jars]
        lhs = sum(lhs_atoms[1:], lhs_atoms[0])
        if isinstance(ineq, GreaterEq): # a * x + b * y + ... ≥ c    
            rhs = Real(ineq.lower_bound)
            hol_ineq = greater_eq(RealType)(lhs, rhs)
            self.ineq_pts[hol_ineq] = ProofTerm.assume(hol_ineq)
        else: # a * x + b * y + ... ≤ c
            rhs = Real(ineq.upper_bound)
            hol_ineq = less_eq(RealType)(lhs, rhs)
            self.ineq_pts[hol_ineq] = ProofTerm.assume(hol_ineq)
        
        # Add the inequation to the simplex solver.
        self.simplex.add_ineq(ineq)
        
        # Check the necessity to introduce new variables
        if not (len(ineq.jars) == 1 and ineq.jars[0].coeff == 1): # need to introduce a new variable
            s = Var('$'+string.ascii_lowercase[self.simplex.index - 1]+'$', RealType)
            s_eq_pt = ProofTerm.assume(Eq(s, lhs))
            self.eq_pts[s] = s_eq_pt
            self.intro_eq.add(s_eq_pt)
            # construct the inequlity proofterm for x
            s_ineq_pt = ProofTerm.assume(hol_ineq).on_prop(top_conv(replace_conv(s_eq_pt.symmetric())))
            self.atom_ineq_pts = add_atom(self.atom_ineq_pts, s, s_ineq_pt)
        else: # directly add x ⋈ c into atom_ineq_pts 
            x = lhs.arg
            # prove 1 * x = x
            pt_x = real.real_norm_conv().get_proof_term(1 * x)
            pt_atom = ProofTerm.assume(hol_ineq).on_prop(top_conv(replace_conv(pt_x)))
            self.atom_ineq_pts = add_atom(self.atom_ineq_pts, x, pt_atom)

    def add_ineqs(self, ineqs):
        for ineq in ineqs:
            self.add_ineq(ineq)
            
    def assert_upper(self, x, upper_bound_pt):
        """
        Assert x <= c. If there is already an assertion on x's upper bound,
        suppose it is d, if c <= d, then apply the new assertion, otherwise 
        still take the old assertion.
        If there is an assertion on x's lower bound, suppose it is e; If e > c,
        then we can derive a direct contradiction: x <= c and x >= e is inconsistency. 
        """
        upper_bound = real.real_eval(upper_bound_pt.prop.arg)
        # assertion = ProofTerm.assume(x <= upper_bound)
        if x in self.upper_bound_pts:
            old_assertion = self.upper_bound_pts[x]
            old_upper_bound = real.real_eval(old_assertion.prop.arg)
            if old_upper_bound >= upper_bound:
                pt_less = ProofTerm('real_compare', less_eq(RealType)(Real(upper_bound), Real(old_upper_bound)))
                self.upper_bound_pts[x] = apply_theorem('real_leq_comp1', upper_bound_pt, old_assertion, pt_less)
            new_upper_bound = upper_bound if (old_upper_bound >= upper_bound) else old_upper_bound
        else:
            self.upper_bound_pts[x] = upper_bound_pt
            new_upper_bound = upper_bound
        

        # check consistency with x's lower bound
        if x in self.lower_bound_pts:
            lower_assertion = self.lower_bound_pts[x]
            lower_bound = real.real_eval(lower_assertion.prop.arg)
            if lower_bound > new_upper_bound: # incosistency
                pt_up_less_low = ProofTerm('real_compare', less(RealType)(Real(new_upper_bound), Real(lower_bound)))
                pt_contr = apply_theorem('real_comp_contr1', pt_up_less_low, lower_assertion, self.upper_bound_pts[x])
                self.unsat[x] = self.elim_aux_vars(pt_contr)
                raise AssertUpperException(str(pt_contr))

        self.simplex.assert_upper(x.name, upper_bound)
        
    def assert_lower(self, x, lower_bound_pt):
        """
        Assert x >= c. If there is already an assertion on x's lower bound,
        suppose it is d, if c >= d, then apply the new assertion, otherwise 
        still take the old assertion.
        If there is an assertion on x's upper bound, suppose it is e: If e < c,
        then we can derive a direct contradiction: x >= c and x <= e is inconsistency. 
        """
        lower_bound = real.real_eval(lower_bound_pt.prop.arg)
        if x in self.lower_bound_pts:
            old_assertion = self.lower_bound_pts[x]
            old_lower_bound = real.real_eval(old_assertion.prop.arg)
            if old_lower_bound <= lower_bound:
                pt_greater = ProofTerm('real_compare', greater_eq(RealType)(Real(lower_bound), Real(old_lower_bound)))
                self.lower_bound_pts[x] = apply_theorem('real_geq_comp2', old_assertion, lower_bound_pt, pt_greater)
            new_lower_bound = lower_bound if (old_lower_bound <= lower_bound) else old_lower_bound
        else:
            self.lower_bound_pts[x] = lower_bound_pt
            new_lower_bound = lower_bound
        

        # check consistency with x's lower bound
        if x in self.upper_bound_pts:
            upper_assertion = self.upper_bound_pts[x]
            upper_bound = real.real_eval(upper_assertion.prop.arg)
            if upper_bound < new_lower_bound: # incosistency
                pt_up_less_low = ProofTerm('real_compare', less(RealType)(Real(upper_bound), Real(new_lower_bound)))
                pt_contr = apply_theorem('real_comp_contr1', pt_up_less_low, self.lower_bound_pts[x], upper_assertion)
                self.unsat[x] = self.elim_aux_vars(pt_contr)
                raise AssertLowerException(str(pt_contr))
        
        self.simplex.assert_lower(x.name, lower_bound)


    def pivot(self, xi, xj, basic_var, coeff):
        """
        Pivot basic variable xi and non-basic variable xj. 
        """

        # Find the xj occurrence in other equalities, try to substitute it by xj's rhs.
        basic_variable_xj_lhs = delete_elem(basic_var, xi.name)
        basic_variable_xj_lhs = [Var(v, RealType) for v in basic_variable_xj_lhs]
        a = coeff # aij
        
        # find the equation: xi = ... + aij * xj + ...
        # aij ≠ 0
        pt_eq = self.eq_pts[xi]
        # convert the equation to xj = ...
        # use theorem: real_sub_0, real_mul
        # xi - (... + aij * xj + ...) = 0
        pt_right_shift = pt_eq.on_prop(rewr_conv('real_sub_0', sym=True))
        # construct (xi - (... + aij * xj + ...)) * 1/aij = 0
        pt_divide_aij = real.real_norm_conv().get_proof_term(Fraction(1, a) * pt_right_shift.lhs)
        # normalize lhs
        pt_divide_aij_norm = pt_divide_aij.on_lhs(real.real_norm_conv())
        
        pt_eq_mul_coeff = apply_theorem('real_times_0', pt_right_shift, inst=Inst(a = Real(Fraction(1, a))))
        pt_divide_aij_norm_0 = pt_divide_aij.symmetric().transitive(pt_eq_mul_coeff)
        # convert to ... + (-1) * xj = 0
        eq_lhs = pt_divide_aij_norm.lhs
        eq_lhs_dest = dest_plus(eq_lhs)
        pt_eq_lhs = real.real_norm_conv().get_proof_term(eq_lhs)
        adder_except_xj = [t if t.is_times() else 1 * t for t in eq_lhs_dest]
        adder_except_xj = [t for t in adder_except_xj if t.arg != xj]
        eq_lhs_xj_right = sum(adder_except_xj[1:], adder_except_xj[0]) + (-1) * xj
        pt_eq_lhs_xj_right = real.real_norm_conv().get_proof_term(eq_lhs_xj_right)
        pt_eq_comm = ProofTerm.transitive(pt_eq_lhs, pt_eq_lhs_xj_right.symmetric())
        pt_comm_eq_0 = pt_eq_comm.symmetric().transitive(pt_divide_aij_norm_0)

        # xj = ... + (1/aij) * xi + ... 
        pt_final = pt_comm_eq_0.on_prop(rewr_conv('real_add_uminus')).symmetric()
        self.eq_pts[xj] = pt_final
        self.eq_pts = delete_key(self.eq_pts, xi)

        # euqalities relevant to xj
        for _v in basic_variable_xj_lhs:
            v_lhs_eq_pt = self.eq_pts[_v]
            v_lhs_eq_pt_replace_norm = v_lhs_eq_pt.on_rhs(top_conv(replace_conv(pt_final)), real.real_norm_conv())
            self.eq_pts[_v] = v_lhs_eq_pt_replace_norm

    def explanation(self):
        """
        Explanation is the core procedure which returns an unsatisfiable proof.
        """
        assert self.simplex.wrong_var is not None, "No var causes contradiction."
        contr_var = Var(self.simplex.wrong_var, RealType)
        unsat_clause = self.simplex.explaination(contr_var.name)

        # Translate unsat clauses into HOL form.
        hol_unsat_upper_bound = dict()
        hol_unsat_lower_bound = dict()
        
        for c in unsat_clause[:-1]:
            if isinstance(c, geq_atom): # x >= k
                var_name, lower_bound = c.var_name, c.lower
                var = Var(var_name, RealType)
                hol_unsat_lower_bound[var] = self.lower_bound_pts[var]
            else:
                var_name, upper_bound = c.var_name, c.upper
                var = Var(var_name, RealType)
                hol_unsat_upper_bound[var] = self.upper_bound_pts[var]                

        if isinstance(unsat_clause[-1], leq_atom): 
            # contradiction comes from contr_var's value is larger than it's upper bound.
            upper_bound_pt = self.upper_bound_pts[contr_var]
            ineq_atom_pts = [] # store a > 0, x >= l ⊢ a * x >= a * l term
            # Get contr_var's lower bound
            for var, upper_bound in hol_unsat_upper_bound.items():
                # the coefficient must < 0, so coeff * upper_bound is coeff * x 's lower bound 
                coeff = self.simplex.aij(contr_var.name, var.name)
                assert coeff < 0
                pt_coeff_less_zero = ProofTerm('real_compare', less(RealType)(Real(coeff), Real(0)))
                # ⊢ x <= u --> a < 0 --> a * u <= a * x
                pt_lower_bound = apply_theorem('real_leq_mul_neg', upper_bound, pt_coeff_less_zero)
                # pt_lower_bound_2 = ProofTerm.implies_elim(upper_bound, pt_lower_bound_1)
                # pt_lower_bound_3 = ProofTerm.implies_elim(pt_coeff_less_zero, pt_lower_bound_2)
                ineq_atom_pts.append(pt_lower_bound)
            
            for var, lower_bound in hol_unsat_lower_bound.items():
                # the coefficient must > 0, so coeff * lower_bound is coeff * x 's lower bound 
                coeff = self.simplex.aij(contr_var.name, var.name)
                assert coeff > 0
                pt_coeff_greater_zero = ProofTerm('real_compare', greater(RealType)(Real(coeff), Real(0)))
                # ⊢ x >= l --> a > 0 --> a * l <= a * x
                pt_lower_bound = apply_theorem('real_geq_mul_pos', lower_bound, pt_coeff_greater_zero)
                # pt_lower_bound_2 = ProofTerm.implies_elim(lower_bound, pt_lower_bound_1)
                # pt_lower_bound_3 = ProofTerm.implies_elim(pt_coeff_greater_zero, pt_lower_bound_2)
                ineq_atom_pts.append(pt_lower_bound)

            # sum contr var atom lower bound to get the total lower bound
            # a < b --> c < d --> a + c < b + d
            sum_pt = ineq_atom_pts[0]
            for pt in ineq_atom_pts[1:]:
                sum_pt = apply_theorem('real_leq_pair_plus', sum_pt, pt)
            
            # combine above pts
            pt_norm_contr_var_rhs = self.eq_pts[contr_var].on_rhs(real.real_norm_conv()).symmetric()
            pt_norm_sum_rhs = sum_pt.on_prop(arg_conv(real.real_norm_conv()))
            pt_comb = pt_norm_sum_rhs.on_prop(top_conv(replace_conv(pt_norm_contr_var_rhs)), arg1_conv(real.real_eval_conv()))

            # after we get contr_var's lower bound(lb), we get lb > β(contr_var), but β(contr_var) > contr_var's upper bound,
            # so we could deriv a contradiction
            lower_bound_value = pt_comb.prop.arg1
            upper_bound_pt = self.upper_bound_pts[contr_var]
            upper_bound_value = upper_bound_pt.prop.arg
            pt_upper_less_lower = ProofTerm('real_compare', upper_bound_value < lower_bound_value)
            pt_concl = self.elim_aux_vars(apply_theorem('real_comp_contr2', pt_upper_less_lower, pt_comb, upper_bound_pt))
            self.unsat[contr_var] = pt_concl

        else: 
            # contradiction comes from contr_var's value is less than it's lower bound.
            lower_bound_pt = self.lower_bound_pts[contr_var]
            ineq_atom_pts = [] # store like a < 0, x >= l ⊢ a * x <= a * l term
            # Get contr_var's upper bound
            for var, upper_bound in hol_unsat_upper_bound.items():
                # the coefficient must > 0, so coeff * upper_bound is coeff * x 's upper bound 
                coeff = self.simplex.aij(contr_var.name, var.name)
                assert coeff > 0
                pt_coeff_greater_zero = ProofTerm('real_compare', greater(RealType)(Real(coeff), Real(0)))
                # ⊢ x <= u --> a > 0 --> a * x <= a * u
                pt_upper_bound = apply_theorem('real_leq_mul_pos', upper_bound, pt_coeff_greater_zero)
                ineq_atom_pts.append(pt_upper_bound)
            
            for var, lower_bound in hol_unsat_lower_bound.items():
                # the coefficient must < 0, so coeff * lower_bound is coeff * x 's upper bound 
                coeff = self.simplex.aij(contr_var.name, var.name)
                assert coeff < 0
                pt_coeff_greater_zero = ProofTerm('real_compare', less(RealType)(Real(coeff), Real(0)))
                # ⊢ x >= l --> a < 0 --> a * x <= a * l
                pt_lower_bound = apply_theorem('real_geq_mul_less', lower_bound, pt_coeff_greater_zero)
                ineq_atom_pts.append(pt_lower_bound)

            # sum contr var atom upper bound to get the total upper bound
            # a < b --> c < d --> a + c < b + d
            sum_pt = ineq_atom_pts[0]
            for pt in ineq_atom_pts[1:]:
                sum_pt = apply_theorem('real_leq_pair_plus', sum_pt, pt)
            
            # combine above pts
            pt_norm_contr_var_rhs = self.eq_pts[contr_var].on_rhs(real.real_norm_conv()).symmetric()
            pt_norm_sum_rhs = sum_pt.on_prop(arg1_conv(real.real_norm_conv()))
            pt_comb = pt_norm_sum_rhs.on_prop(top_conv(replace_conv(pt_norm_contr_var_rhs)), arg_conv(real.real_eval_conv()))

            # after we get contr_var's upper bound(ub), we get lb > β(contr_var), but β(contr_var) > contr_var's upper bound,
            # so we could deriv a contradiction
            upper_bound_value = pt_comb.prop.arg
            lower_bound_pt = self.lower_bound_pts[contr_var]
            lower_bound_value = lower_bound_pt.prop.arg
            pt_upper_less_lower = ProofTerm('real_compare', upper_bound_value < lower_bound_value)
            pt_concl = self.elim_aux_vars(apply_theorem('real_comp_contr1', pt_upper_less_lower, lower_bound_pt, pt_comb))            
            self.unsat[contr_var] = pt_concl

        return self.normalize_conflict_pt(pt_concl)

    def elim_aux_vars(self, pt):
        for eq in self.intro_eq:
            eq = eq.prop
            pt = pt.implies_intr(eq).forall_intr(eq.lhs).forall_elim(eq.rhs).implies_elim(ProofTerm.reflexive(eq.rhs))
        return pt

    def normalize_conflict_pt(self, pt_concl):
        """
        Convert all x to 1 * x in the UNSAT proof term.
        """
        # rewrite 1 * x to x in hyps
        for hyp in pt_concl.hyps:
            pt_concl = pt_concl.implies_intr(hyp)
        pt_concl = pt_concl.on_prop(bottom_conv(rewr_conv('real_mul_lid')))
        imps, _ = pt_concl.prop.strip_implies()

        for ii in imps:
            pt_concl = pt_concl.implies_elim(ProofTerm.assume(ii))

        return pt_concl

    
    def handle_assertion(self):
        """
        Assert each atom assertion, either get a bound or raise a contradiction.
        """
        for var, asts in self.atom_ineq_pts.items():
            for ast in asts:
                try:
                    if ast.prop.is_less_eq():
                        self.assert_upper(var, ast)
                    else:
                        self.assert_lower(var, ast)
                except (AssertLowerException, AssertUpperException):
                    return self.normalize_conflict_pt(self.unsat[var])
            # if var.name in self.simplex.basic:
                # check
                if self.simplex.check() == UNSAT:
                    trace = self.simplex.trace
                    # print("trace: ", trace)
                    # print("self", self)
                    # print("self.simplex: ", self.simplex)
                    # print("wrong_var: ", self.simplex.wrong_var)
                    for xij, coeff, basic_var in trace:
                        xi, xj = xij
                        self.pivot(Var(xi, RealType), Var(xj, RealType), basic_var, coeff)
                    return self.normalize_conflict_pt(self.explanation())
                    raise UNSATException("%s" % str(self.unsat[Var(self.simplex.wrong_var, RealType)]))

        return self.simplex.mapping


def term_to_ineq(tms):
    """Convert a list inequalities into a tableau."""
    vs = dict()
    i = 0
    tableau = []
    new_tms = [] # store the HOL form of standard tableau
    for tm in tms:
        summands = [(real.real_eval(t.arg1), t.arg) if t.is_times() else (1, t) for t in dest_plus(tm.arg1)]
        line = []
        for coeff, v in summands:
            if v not in vs:
                new_var = "x_" + str(i)
                i += 1
                vs[v] = new_var
                line.append(Jar(coeff, new_var))
            else:
                line.append(Jar(coeff, vs[v]))
        bound = real.real_eval(tm.arg)

        left_parts = [jar.coeff * Var(jar.var, RealType) if jar.coeff != 1 else Var(jar.var, RealType) for jar in line]
        hol_sum = sum(left_parts[1:], left_parts[0])

        if tm.is_less_eq():
            tableau.append(LessEq(line, bound))
            new_tms.append(hol_sum <= bound)
        elif tm.is_greater_eq():
            tableau.append(GreaterEq(line, bound))
            new_tms.append(hol_sum >= bound)
        else:
            raise NotImplementedError

    return tableau, new_tms, {Var(value, RealType): key for key, value in vs.items()}

@register_macro("simplex_macro")
class SimplexMacro(Macro):
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None

    def get_proof_term(self, args, prevs=None):
        # assume that all inequalities have been in normal form:
        # args = [ineq1, ineq2,...]
        solver = SimplexHOLWrapper()
        # first give each variable in inequality a new name in case of 
        # illusion from ite term
        comparisons, new_args, subst_vars = term_to_ineq(args)
        solver.add_ineqs(comparisons)
        result = solver.handle_assertion()
        if not isinstance(result, ProofTerm):
            print("SAT")
            return result
        # P_1, P_2, ... |- false
        pt_0 = result
        # |- P_1 --> P_2 --> ... --> false 
        pt_1 = functools.reduce(lambda x, y: x.implies_intr(y), pt_0.hyps, pt_0)
        # substitution
        pt_eqs = [ProofTerm.assume(Eq(key, value)) for key, value in subst_vars.items()]
        pt_2 = functools.reduce(lambda x, y: x.on_prop(top_conv(replace_conv(y))), pt_eqs, pt_1)
        # eliminate auxiliary equalities
        pt_3 = pt_2
        for pt_eq in pt_eqs:
            eq = pt_eq.prop
            pt_3 = pt_3.implies_intr(eq).forall_intr(eq.lhs).forall_elim(eq.rhs).implies_elim(ProofTerm.reflexive(eq.rhs))

        pt_4 = pt_3

        preds, _ = pt_4.prop.strip_implies()
        pt_5 = functools.reduce(lambda x, y: x.implies_elim(ProofTerm.assume(y)), preds, pt_4)
        return pt_5

@register_macro("integer_simplex")
class IntegerSimplexMacro(Macro):
    def __init__(self):
        self.level = 0
        self.sig = Term
        self.limit = None
    
    def get_proof_term(self, args, prevs=None):
        # assume that all inequalities have been in normal form:
        # args = [ineq1, ineq2,...]
        # first convert every integer term to of_int term
        pt_of_int = [integer.int_compare_to_real().get_proof_term(ineq).symmetric() for ineq in args]
        real_ineqs = [pt.lhs for pt in pt_of_int]
        # give each of_int term a new name
        comparisons, new_args, subst_vars = term_to_ineq(args)
        # get result
        s = Simplex()
        s.add_ineqs(*comparisons)
        T = branch_and_bound(s)
        result = T.branch_and_bound_pt()
        if not isinstance(result, ProofTerm):
            print("SAT")
            return result
        # P_1, P_2, ... |- false
        pt_0 = result
        # |- P_1 --> P_2 --> ... --> false 
        pt_1 = functools.reduce(lambda x, y: x.implies_intr(y), pt_0.hyps, pt_0)
        # substitution
        pt_eqs = [ProofTerm.assume(Eq(key, of_int(RealType)(value))) for key, value in subst_vars.items()]
        pt_2 = functools.reduce(lambda x, y: x.on_prop(top_conv(replace_conv(y))), pt_eqs, pt_1)
        # eliminate auxiliary equalities
        pt_3 = pt_2
        for pt_eq in pt_eqs:
            eq = pt_eq.prop
            pt_3 = pt_3.implies_intr(eq).forall_intr(eq.lhs).forall_elim(eq.rhs).implies_elim(ProofTerm.reflexive(eq.rhs))

        pt_4 = pt_3

        preds, _ = pt_4.prop.strip_implies()
        pt_5 = functools.reduce(lambda x, y: x.implies_elim(ProofTerm.assume(y)), preds, pt_4)

        # |- P_1 --> P_2 --> ... --> false 
        pt_6= functools.reduce(lambda x, y: x.implies_intr(y), pt_5.hyps, pt_5)
        # convert all of_int terms to original terms
        pt_of_int_1 = [pt.on_lhs(top_conv(real.real_eval_conv()), bottom_conv(rewr_conv('real_mul_lid'))) for pt in pt_of_int]
        pt_7 = pt_6.on_prop(*[top_conv(replace_conv(pt)) for pt in pt_of_int_1])
        implies_int_ineqs, _ = pt_7.prop.strip_implies()
        return functools.reduce(lambda x, y: x.implies_elim(ProofTerm.assume(y)), implies_int_ineqs, pt_7)