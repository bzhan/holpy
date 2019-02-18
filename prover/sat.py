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
    def str_of_literal(a, b):
        # Change [('x', False)] to ~x, change [('x', True)] to x.
        if not b:
            return '~' + a
        else:
            return a

    def str_of_clause(clause):
        # Turn clause to string by adding (,|,)
        return ' | '.join(str_of_literal(a, b) for a, b in clause)

    if len(cnf) == 0:
        return 'empty set'

    if any(len(clause) == 0 for clause in cnf):
        return 'the CNF contains empty clause'

    if len(cnf) == 1:
        return str_of_clause(cnf[0])

    cnf1 = []
    for num_c, clause in enumerate(cnf):
        cnf1.append(str_of_clause(clause))
        if len(clause) >= 2:
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
    cnf1 = []
    for num_c, clause in enumerate(cnf):
        cnf1.append([])
        for a, b in clause:
            #inst doesn't contain assignment for all variables
            if not a in inst:
                raise SATSolverException
            #the literal is assigned True,so the clause is satisfiable
            if inst[a] == b:
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
    
    Turn res to the standard form
    
    """
    # print(solve_cnf1(cnf))
    res, _, _ = solve_cnf1(cnf)
    if res is None:
        return None
    else:
        return dict((x, res[x][2]) for x in res)

def solve_cnf1(cnf):
    """Solve the given CNF by clause learning
    
    for each assigned variable x, res[x] is a list of three things:
    1. the assert level
    2. Is x an inferred variable (False) or an assumed variable (True)
    3. x's value (True or False)
    for example, res[x] = [1, True, True] means x is assumed at assert level 1, and x is assigned True

    """
    implication_graph = OrderedDict()
    learn_CNF = []
    res = OrderedDict()
    assert_level = 0
    L = len(cnf)

    #empty set
    if L == 0:
        return res, learn_CNF, implication_graph

    #cnf contains the empty set
    for num_c, clause in enumerate(cnf):
        if len(clause) == 0:
            #'C' means original CNF, 'L' means learn_CNF, None means the conflict
            implication_graph[None] = ['C', num_c, assert_level]
            return None, learn_CNF, implication_graph
    
    buc = bucket(cnf)
    affect_clauses = []

    #every clauses needs to be checked the first time
    for i in range(len(cnf)):
        affect_clauses.append(i)
    
    return solve_cnf_rec(cnf, L, learn_CNF, buc, assert_level, res, implication_graph, affect_clauses)
    

def solve_cnf_rec(cnf, L, learn_CNF, buc, assert_level, res, implication_graph, affect_clauses):
    if affect_clauses == []:
        if len(res) == len(buc):
            return res, learn_CNF, implication_graph
        else:
            #assume a variable's value
            for x in buc:
                if not x in res:
                    assert_level += 1
                    res[x] = [assert_level, True, True]
                    for num_c in buc[x]:
                        affect_clauses.append(num_c)
                    return solve_cnf_rec(cnf, L, learn_CNF, buc, assert_level, res, implication_graph, affect_clauses)

    affect_clauses_new = []

    for num_c in affect_clauses:
        #num_c1 shows the clause number in original CNF or learn_CNF
        if num_c <= L - 1:    
            clause_place = 'C'
            num_c1 = num_c
            clause = cnf[num_c1]
        else:
            clause_place = 'L'
            num_c1 = num_c - L
            clause = learn_CNF[num_c1]            
        
        check = check_clause(clause, res)
        if check == False:
            implication_graph[None] = [clause_place, num_c1, assert_level]

            #UNSAT
            if assert_level == 0:
                return None, learn_CNF, implication_graph
            
            #clause learning and modify the buc
            num_1 = len(learn_CNF)
            num = num_1 + L
            learn_clause = []
            for x in res:
                if res[x][1] == True:
                    learn_clause.append((x, not res[x][2]))
                    buc[x].append(num)
            learn_CNF.append(learn_clause)

            # Find the minimum assert level (except 0) in the complict clause,
            # and backtrack to this level.
            min_level = min(res[a][0] for a, b in clause if res[a][0] != 0)

            if len(learn_clause) == 1:
                # When the learned clause has only one variable x, x's value can be
                # inferred from this clause. 
                while len(implication_graph) != 0:
                    x, [x_clause_place, x_num_c1, x_assert_level] = implication_graph.popitem()
                    if x_assert_level < min_level:
                        implication_graph[x] = [x_clause_place, x_num_c1, x_assert_level]
                        break
                
                while True:
                    x, [x_assert_level, x_if_assume, x_value] = res.popitem()
                    if x_if_assume:
                        res[x] = [min_level - 1, False, not x_value]
                        affect_clauses_new = buc[x]
                        implication_graph[x] = ['L', num_1, min_level - 1]
                        break

                return solve_cnf_rec(cnf, L, learn_CNF, buc, min_level - 1, res, implication_graph, affect_clauses_new)

            #backtrack, change res and implication graph
            while True:
                x, [x_assert_level, x_if_assume, x_value] = res.popitem()
                if x_if_assume == True and x_assert_level == min_level:
                    res[x] = [min_level, True, not x_value]
                    affect_clauses_new = buc[x]
                    break

            while len(implication_graph) != 0:
                x, [x_clause_place, x_num_c1, x_assert_level] = implication_graph.popitem()
                if x_assert_level < min_level:
                    #one more element is deleted, so add it back
                    implication_graph[x] = [x_clause_place, x_num_c1, x_assert_level]
                    break

            return solve_cnf_rec(cnf, L, learn_CNF, buc, min_level, res, implication_graph, affect_clauses_new)

        elif check == None:
            continue
        else:
            unit_variable, unit_value = check
            if not unit_variable in res:
                res[unit_variable] = [assert_level, False, unit_value]
                implication_graph[unit_variable] = [clause_place, num_c1, assert_level]
                for num in buc[unit_variable]:
                    if num not in affect_clauses_new:
                        affect_clauses_new.append(num)
    
    return solve_cnf_rec(cnf, L, learn_CNF, buc, assert_level, res, implication_graph, affect_clauses_new)

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