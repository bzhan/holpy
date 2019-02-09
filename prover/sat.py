from collections import OrderedDict

"""
Implementation of SAT solver.

CNFs are represented using lists of lists of literals, where
each literal is given by a pair (x, b), where x is a string
(name of the boolean variable), and b is a boolean value giving
the sign of the literal.

For example, (~x | y) & (~y | z) is represented as
[[('x', False), ('y', True)], [('y', False), ('z', True)]].

"""

class SATSolverException(Exception):
    pass


def display_cnf(cnf):
    """Display the given CNF."""
    cnf1 = []
    if len(cnf) == 0:
        return 'empty set'
    for num_c, clause in enumerate(cnf):
        L = len(clause)
        if L == 0:
            return 'the CNF contains empty clause'

        cnf1.append([])
        #change [('x', False)]to ~x ,change [('x', True)]to x
        for (a, b) in clause:
            if not b:
                literal = '~' + a
            else:
                literal = a
            cnf1[num_c].append(literal)

        #turn literals to clause by adding (,|,)
        cnf1[num_c]=' | '.join(cnf1[num_c])
        if num_c == 0 and len(cnf) == 1:
            return cnf1[0]
        elif L >= 2:
            cnf1[num_c] = '(' + cnf1[num_c] + ')'
    return ' & '.join(cnf1)

def is_solution(cnf, inst):
    """Determines whether the given instantiation is a solution to
    the CNF.
    
    inst is a dictionary representing the satisfying assignment. It
    must contain assignment for all variables.
    
    Raises SATSolverException if inst does not contain assignment
    for some variable.
    
    """
    cnf1=[]
    for num_c, clause in enumerate(cnf):
        cnf1.append([])
        for (a, b) in clause:
            #inst doesn't contain assignment for all variables
            if not a in inst:
                raise SATSolverException
            #the literal is assigned True,so the clause is satisfiable
            if inst[a] - b == 0:
                cnf1[num_c].append(True)
            else:
                cnf1[num_c].append(False)
        cnf1[num_c] = any(cnf1[num_c])
    return all(cnf1)

def bucket(cnf):
    '''create a bucket Bx for each variable x'''
    Buckets = {}
    for num_c, clause in enumerate(cnf):
        for literal in clause:
            a = literal[0]
            if not a in Buckets:
                Buckets[a]=[num_c]
            else:
                Buckets[a].append(num_c)
    return Buckets

def solve_cnf(cnf):
    """Solve the given CNF.
    
    If the CNF is satisfiable, returns the satisfying assignment
    as a dictionary.
    
    Otherwise, return None.
    
    for each assigned variable x, res[x] is a list of three things:
    1. the assert level
    2. Is x an inferred variable (False) or an assumed variable (True)
    3. x's value (True or False)
    for example, res[x] = [1, True, True] means x is assumed at assert level 1, and x is assigned True

    """
    res = OrderedDict()
    
    #empty set
    if len(cnf) == 0:
        return res

    #cnf contains the empty set
    for clause in cnf:
        if len(clause) == 0:
            return None
    
    assert_level = 0
    buc = bucket(cnf)
    #every clauses needs to be checked the first time
    affect_clauses = []
    for i in range(len(cnf)):
        affect_clauses.append(i)

    #turn res to the standard form
    res = solve_cnf_rec(cnf, buc, assert_level, res, affect_clauses)
    if res == None:
        return None
    else:
        res1 = {}
        for x in res:
            res1[x] = res[x][2]
        return res1

def solve_cnf_rec(cnf, buc, assert_level, res, affect_clauses):
    if affect_clauses == []:
        if len(res) == len(buc):
            return res
        else:
            #assume a variable's value
            for x in buc:
                if not x in res:
                    assert_level += 1
                    res[x] = [assert_level, True, True]
                    for num_c in buc[x]:
                        affect_clauses.append(num_c)
                    return solve_cnf_rec(cnf, buc, assert_level, res, affect_clauses)

    affect_clauses_new = []

    for num_c in affect_clauses:
        check = check_clause(cnf[num_c], res)
        if check == False:
            #show the contradiction
            print(res)
            print(num_c)
            #backtrace
            if_stop = False
            while(if_stop == False):
                x, [a, b, c] = res.popitem(last=True)
                if b == True and c == True:
                    if_stop = True
                    assert_level = a
                    res[x] = [assert_level, True, False]
                    affect_clauses_new = buc[x]
                    return solve_cnf_rec(cnf, buc, assert_level, res, affect_clauses_new)
                if len(res) == 0:
                    return None

        elif check == None:
            continue
        else:
            a, b = check
            if not a in res:
                res[a] = [assert_level, False, b]
                for num in buc[a]:
                    if num not in affect_clauses_new:
                        affect_clauses_new.append(num)
    
    return solve_cnf_rec(cnf, buc, assert_level, res, affect_clauses_new)

def check_clause(clause, res):
    """Check the clause

    If the clause infers contradiction, return False
    
    If the clause only has one unassigned valuable, use unit resolution, return the valuable and it's assignment
    
    Else, we can't get anything useful from this clause, return None

    """
    num_unassigned = 0
    clause_value = 0
    unit_variable, unit_value = None, None
    for (a, b) in clause:
        if a in res:
            if b == res[a][2]:
                clause_value = 1

        if not a in res:
            if num_unassigned == 0:
                unit_variable, unit_value = a, b
                num_unassigned = 1
            else: 
                return None

    if num_unassigned == 1 and clause_value == 0:
        return unit_variable, unit_value
    else:
        if clause_value == 0:
            return False
        else:
            return None