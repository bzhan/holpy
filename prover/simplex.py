"""
Implementation of Simplex-based quantifier-free linear arithmetic solver.

Reference: 
Bruno Dutertre and Leonardo de Moura. A Fast Linear-Arithmetic Solver for DPLL(T) 
"""

from collections import namedtuple
import math
import numbers
import string
from fractions import Fraction

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
    def __init__(self, *args, **kwargs):
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
        self.jars = jars
        self.lower_bound = lower_bound

    def __str__(self):
        return " + ".join([str(jar) for jar in self.jars]) + " >= " + str(self.lower_bound)
        


class LessEq(InEquation):
    """Represent a greater equality term."""
    def __init__(self, jars, upper_bound):
        assert(all(isinstance(j, Jar) for j in jars))
        assert(isinstance(upper_bound, numbers.Number))
        self.jars = jars
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
    def __init__(self):
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
        self.orginal = []

    def __str__(self):
        s = "Original inequlities: \n"
        for ineq in self.orginal:
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
        self.orginal.append(ineq)
        if isinstance(ineq, GreaterEq):
            if len(ineq.jars) == 1: # a * x >= b
                jar = ineq.jars[0]
                coeff, var_name, lower_bound = jar.coeff, jar.var, ineq.lower_bound
                if coeff == 1: # x >= b (atom)
                    self.lower_atom.append((var_name, lower_bound))
                    self.atom.append(geq_atom(var_name, lower_bound))
                    if var_name not in self.mapping:
                        self.mapping[var_name] = 0
                    self.non_basic.add(var_name)
                    if var_name not in self.bound.keys():
                        self.bound[var_name] = (-math.inf, math.inf)

                elif coeff != 0: # a * x >= b
                    s = "?" + string.ascii_lowercase[self.index]
                    self.index += 1
                    self.lower_atom.append((s, lower_bound))
                    self.atom.append(geq_atom(s, lower_bound))
                    self.equality[s] = ineq.jars
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

                lower_bound = ineq.lower_bound
                s = "?" + string.ascii_lowercase[self.index]
                self.index += 1
                self.equality[s] = ineq.jars
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
                if coeff == 1: # x <= b (atom)
                    self.upper_atom.append((var_name, upper_bound))
                    self.atom.append(leq_atom(var_name, upper_bound))
                    if var_name not in self.mapping:
                        self.mapping[var_name] = 0
                    self.non_basic.add(var_name)
                    if var_name not in self.bound.keys():
                        self.bound[var_name] = (-math.inf, math.inf)

                elif coeff != 0: # a * x <= b
                    s = "?" + string.ascii_lowercase[self.index]
                    self.index += 1
                    self.upper_atom.append((s, upper_bound))
                    self.atom.append(leq_atom(s, upper_bound))
                    self.equality[s] = ineq.jars
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

                upper_bound = ineq.upper_bound
                s = "?" + string.ascii_lowercase[self.index]
                self.index += 1
                self.equality[s] = ineq.jars
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
        equlity_has_xj = []
        for x in self.nbasic_basic[xj]:
            if x != xi:
                rhs = self.equality[x]
                _, xj_jar = find_coeff(xj, rhs)
                rhs_without_xj = reduce_pairs([j for j in rhs if j != xj_jar] + xj_repr_jars)
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
        self.mapping[xj] = self.mapping[xi] + theta
        for xk in self.basic:
            if xk != xi:
                k = self.aij(xk, xj)
                self.mapping[xk] += k * theta

        self.pivot(xi, xj)

    def assert_upper(self, x, c):
        assert x in self.bound, "No such variable in solver"
        l, u = self.bound[x]
        if c >= u:
            return
        elif c < l:
            raise AssertUpperException("%s's lower bound %s is larger than %s" % (x, str(l), str(c)))
        
        self.bound[x] = (l, c)
        if x in self.non_basic and self.mapping[x] > c:
            self.update(x, c)

    def assert_lower(self, x, c):
        assert x in self.bound, "No such variable in solver"
        l, u = self.bound[x]
        if c <= l:
            return
        elif c > u:
            raise AssertUpperException("%s's lower bound %s is larger than c" % (x, str(l), str(c)))
        
        self.bound[x] = (c, u)
        if x in self.non_basic and self.mapping[x] < c:
            self.update(x, c)

    def check(self):
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
                        self.pivotAndUpdate(xi, xj, self.bound[xi][0])
                        flag = True
                        break
                if not flag:
                    return UNSAT

            if self.mapping[xi] > self.bound[xi][1]:
                flag = False
                rhs_jars = reduce_pairs(self.equality[xi])
                for j in rhs_jars:
                    coeff, xj = j.coeff, j.var
                    if coeff < 0 and self.mapping[xj] < self.bound[xj][1] or\
                        coeff > 0 and self.mapping[xj] > self.bound[xj][0]:
                        self.pivotAndUpdate(xi, xj, self.bound[xi][1])
                        flag = True
                        break
                
                if not flag:
                    return UNSAT

    def handle_assertion(self):
        for assertion in self.atom:
            if isinstance(assertion, leq_atom):
                self.assert_upper(assertion.var_name, assertion.upper)
                
            else:
                self.assert_lower(assertion.var_name, assertion.lower)

            if assertion.var_name in self.basic:
                res = self.check()
                if res == UNSAT:
                    raise UNSATException

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
    return (tm.arg1, tm.arg2)
