from fractions import Fraction
from collections.abc import Iterable

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

class Pair:
    def __init__(self, x, y=None):
        assert isinstance(x, (int, Fraction))
        self.x = Fraction(x)
        if y is None:
            self.y = Fraction(0)
        else:
            assert isinstance(y, (int, Fraction))
            self.y = Fraction(y)

    def __repr__(self):
        return "(%s, %s)" % (self.x, self.y)

    def __str__(self):
        return "%s + %sδ" % (self.x, self.y)

    def __eq__(self, other):
        assert isinstance(other, Pair)
        return self.x == other.x and self.y == other.y

    def __add__(self, other):
        assert isinstance(other, Pair)
        return Pair(self.x + other.x, self.y + other.y)

    def __mul__(self, a):
        assert isinstance(a, (int, Fraction))
        a = Fraction(a)
        return Pair(a * self.x, a * self.y)

    def __sub__(self, other):
        assert isinstance(other, Pair)
        return Pair(self.x - other.x, self.y - other.y)
    
    def __le__(self, other):
        assert isinstance(other, Pair)
        return self.x < other.x or (self.x == other.x and self.y <= other.y)

    def __ge__(self, other):
        assert isinstance(other, Pair)
        return self.x > other.x or (self.x == other.x and self.y >= other.y)        

    def __hash__(self):
        return hash((self.x, self.y))

def binary_delta(p1, p2):
    """Given two pairs (x_1, y_1) and (x_2, y_2), where (x_1, y_1) ≤ (x_2, y_2),
    return a δ_0 which satisfies x_1 + y_1 * δ_0 ≤ x_2 + y_2 * δ_0. 
    """
    assert p1 <= p2, "%s is larger than %s" % (p1, p2)

    if p1.x < p2.x and p1.y > p2.y:
        return Fraction(p2.x - p1.x, p1.y - p2.y)
    else:
        return 1

def multi_delta(*ps):
    """ps is a list of m pairs of Pair: ((c_1, k_1), (d_1, h_1)) ... ((c_m, k_m), (d_m, h_m))
    return min{(d_i - c_i)/(k_i - h_i) | c_i < d_i and k_i > h_i}
    """
    d = set()
    for p1, p2 in ps:
        if p1 <= p2:
            d.add(binary_delta(p1, p2))

    return min(d) if d else 1

def collect_pairs(ps):
    """Reduce a list of pairs by collecting into groups according to
    first components, and adding the second component for each group.

    It is assumed that the first components are hashable.

    e.g. [("x", 1), ("y", 2), ("x", 3)] => [("x", 4), ("y", 2)]

    """
    res = {}
    for v, c in ps:
        if v in res:
            res[v] += c
        else:
            res[v] = c
    return tuple(sorted((k, Fraction(v)) for k, v in res.items() if v != 0))

class LinearExpr:
    """Represent a linear expression."""
    def __init__(self, tms):
        assert isinstance(tms, Iterable) and all(isinstance(v, str) and isinstance(a, (int, Fraction)) for 
                v, a in tms)
        self.tms = collect_pairs(tms)

    def __str__(self):
        return " + ".join("%s × %s" % (a, b) for b, a in self.tms)

    def __repr__(self):
        return repr(self.tms)

    def __hash__(self):
        return hash(("Linear", self.tms))

    def __len__(self):
        return len(self.tms)

class InEquation:
    def __init__(self, lexpr, bound):
        assert isinstance(lexpr, LinearExpr) and isinstance(bound, Pair)
        self.lexpr = lexpr
        self.bound = bound

class Lower(InEquation):
    def __init__(self, lexpr, bound):
        super().__init__(lexpr, bound)

    def __str__(self):
        return "%s ≤ %s" % (self.lexpr, self.bound)

    def __hash__(self):
        return hash(("LOWER", self.lexpr, self.bound))

class Upper(InEquation):
    def __init__(self, lexpr, bound):
        super().__init__(lexpr, bound)

    def __str__(self):
        return "%s ≥ %s" % (self.lexpr, self.bound)

    def __hash__(self):
        return hash(("UPPER", self.lexpr, self.bound))

class Simplex:
    """"""
    def __init__(self, ilp=False):
        # table represents the solver current tableau(state)
        self.equality = dict()

        # # elementary atoms: y ⋈ b
        # self.lower_atom = [] # y >= b
        # self.upper_atom = [] # y <= b
        # self.atom = []

        # mapping from basic variables to assertions
        self.assertions = dict()
        
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
        assert isinstance(ineq, InEquation)
        self.original.append(ineq)
        if len(ineq) == 1: # a * x ⋈ c
            coeff, var_name, bound = ineq.tms[0][1], ineq.tms[0][0], ineq.bound
            self.input_vars.add(var_name)
            if coeff == 1: # x ⋈ c
                # add it to assertions
                # map x to 0, and set its bound to 
                pass
            else:
                pass

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
