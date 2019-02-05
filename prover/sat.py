from copy import deepcopy

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
    cnf1 = deepcopy(cnf)
    if len(cnf1) == 0:
        return 'empty set'
    for num_c, clause in enumerate(cnf1):
        L = len(clause)
        if L == 0:
            return 'the CNF contains empty clause'

        #change [('x', False)]to ~x ,change [('x', True)]to x
        for num_l, (a, b) in enumerate(clause):
            if not b:
                literal = '~' + a
            else:
                literal = a
            clause[num_l] = literal

        #turn literals to clause by adding (,|,)
        cnf1[num_c]=' | '.join(clause)
        if num_c == 0 and len(cnf1) == 1:
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
    cnf1=deepcopy(cnf)
    for num_c, clause in enumerate(cnf1):
        for num_l, (a, b) in enumerate(clause):
            #inst doesn't contain assignment for all variables
            if not a in inst:
                raise SATSolverException
            #the literal is assigned True,so the clause is satisfiable
            if inst[a] - b == 0:
                clause[num_l] = True
            else:
                clause[num_l] = False
        cnf1[num_c] = any(clause)
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

def replace(cnf, x, y, buc):
    """Replacing evering occurrence of variable x
    
    x is a variable, y is a boolean variable, 
    buc is the bucket of the cnf
    the clause in cnf could be None

    """
    cnf1 = deepcopy(cnf)
    buc1 = deepcopy(buc)
    if x not in buc:
        return cnf1, buc1

    for num_c in buc1[x]:
        if cnf1[num_c] == None:
            continue
        clause_new = []
        for (a, b) in cnf1[num_c]:
            #delete the cnf and modify the buc
            if a == x and b == y:
                for (a, b) in cnf1[num_c]:
                    if a != x:
                        buc1[a].remove(num_c)
                        if buc1[a] == []:
                            del buc1[a]
                clause_new = None
                break
            #delete the literal assigned False
            elif a != x:
                clause_new.append((a,b))
        cnf1[num_c] = clause_new
    del buc1[x]
    return cnf1, buc1

def solve_cnf(cnf):
    """Solve the given CNF.
    
    If the CNF is satisfiable, returns the satisfying assignment
    as a dictionary.
    
    Otherwise, return None.
    
    """
    res={}
    cnf1 = deepcopy(cnf)
    buc = bucket(cnf1)
    res_new = solve_cnf_rec(cnf1, buc, res)
    #assign the unassigned variables
    if res_new != None:
        for x in buc:
            if not x in res_new:
                res_new[x] = True
    return res_new

def solve_cnf_rec(cnf, buc, res):
    #empty set
    cnf1 = deepcopy(cnf)
    buc1 = deepcopy(buc)
    res1 = deepcopy(res)

    if len(cnf1) == 0:
        return(res1)

    #empty set(only has None clause)
    is_empty_set = 1
    for clause in cnf1:
        if clause != None:
            is_empty_set = 0
            break
    if is_empty_set == 1:
        return(res1)

    #cnf contains the empty set
    for clause in cnf1:
        if clause == None:
            continue
        if len(clause) == 0:
            return None
    
    #x only appears in one clause
    for x in buc1:
        if len(buc1[x]) == 1:
            for (a, b) in cnf1[buc[x][0]]:
                #when b is True,x is assigned True; when b is False,x is assigned False
                if a == x:
                    res1[x] = b
                    break
            cnf_new, buc_new = replace(cnf1, x, res1[x], buc1)
            if solve_cnf_rec(cnf_new, buc_new, res1) != None:
                return dict(res1, **solve_cnf_rec(cnf_new, buc_new, res1))
            else:
                return None
                
    #unit resolution
    for clause in cnf1:
        if clause == None:
            continue
        if len(clause) == 1:
            #when the clause is [('x',True)],assigned x True;when the clause is [('x',False)],assigned x False;
            res1[clause[0][0]] = clause[0][1]
            cnf_new, buc_new=replace(cnf1, clause[0][0], clause[0][1], buc1)
            if solve_cnf_rec(cnf_new, buc_new, res1) != None:
                return dict(res1, **solve_cnf_rec(cnf_new, buc_new, res1))
            else:
                return None
    
    #assume a variable's value
    m = list(buc1.keys())[0]

    cnf_new1, buc_new1 = replace(cnf1, m, True, buc1)
    cnf_new2, buc_new2 = replace(cnf1, m, False, buc1)
    if solve_cnf_rec(cnf_new1, buc_new1, res1) != None:
        res1[m] = True
        return dict(res1, **solve_cnf_rec(cnf_new1, buc_new1, res1))
    elif solve_cnf_rec(cnf_new2, buc_new2, res1) != None:
        res1[m]=False
        return dict(res1, **solve_cnf_rec(cnf_new2, buc_new2, res1))
    else:
        return None