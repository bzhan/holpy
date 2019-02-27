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
    """create a bucket Bx for each variable x"""
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
    """Solve the given CNF

    If the CNF is satisfiable, returns the satisfying assignment
    as a dictionary.
    
    Otherwise, return None.

    """
    if_SAT, _, implication_graph, _ = solve_cnf1(cnf)
    if not if_SAT:
        return None
    
    #Turn implication graph to the standard form
    else:
        return dict((x, implication_graph[x][1]) for x in implication_graph)


def solve_cnf1(cnf):
    """Solve the given CNF by clause learning.

    record the implication graph and the process of learning clauses
    
    """
    L = len(cnf)
    assertion_level = 0
    learn_CNF = []
    if_SAT = True
    
    #for a varieble x, implication_graph[x] records: 
        #whether x is set by a decision(True) or an implication(None)
        #x's value
        #x's assertion level
        #when x is set by an implication, it also records which clause x is inferred from
    #it should be noted that when a contradiction is inferred, it's recorded as implication_graph[None]
    implication_graph = OrderedDict()
    
    #clauses_sourse record the process of learning clauses
    clauses_sourse = []
    
    #empty set
    if L == 0:
        return if_SAT, learn_CNF, implication_graph, clauses_sourse

    for num_c, clause in enumerate(cnf):
        if len(clause) == 0:
            if_SAT = False
            implication_graph[None] = [None, None, assertion_level, num_c]
            clauses_sourse.append(num_c)
            return if_SAT, learn_CNF, implication_graph, clauses_sourse

    buc = bucket(cnf)
    affect_clauses = []

    #every clauses needs to be checked for the first time
    for i in range(L):
        affect_clauses.append(i)
    
    #record whether the loop ends
    flag = True
    
    def find_clause(num):
        nonlocal L, cnf, learn_CNF
        if num <= L - 1:
            return cnf[num]
        else:
            return learn_CNF[num - L]

    
    
    def operate():
        nonlocal cnf, L, learn_CNF, buc, if_SAT, assertion_level, implication_graph, affect_clauses, clauses_sourse, flag
        
        if affect_clauses == []:
            if len(implication_graph) == len(buc):
                flag = False
                return
            
            #assume a variable's value
            for x in buc:
                if not x in implication_graph:
                    assertion_level +=1
                    implication_graph[x] = [True, True, assertion_level, None]
                    for num_c in buc[x]:
                        affect_clauses.append(num_c)
                    return
            
        affect_clauses_new = []
        
        for num_c in affect_clauses:
            clause = find_clause(num_c)
            check = check_clause(clause, implication_graph)

            if check == False:
                implication_graph[None] = [None, None, assertion_level, num_c]

                #UNSAT
                if assertion_level == 0:
                    flag = False
                    if_SAT = False
                    process = [num_c]
                    for a, _ in find_clause(num_c):
                        process.append([a,implication_graph[a][3]])
                    clauses_sourse.append(process)
                    return
                
                #clause learning, modify the buc and clauses_sourse
                learn_variables_list = []
                for a, _ in clause:
                    if a not in learn_variables_list:
                        learn_variables_list.append(a)
                process=[num_c]

                while not all(implication_graph[a][0] for a in learn_variables_list):
                    for a in learn_variables_list:
                        if not implication_graph[a][0]:
                            if assertion_level == 0:
                                learn_variables_list.remove(a)
                                process.append([a, implication_graph[a][3]])
                                break
                            else:
                                clause1 = find_clause(implication_graph[a][3])
                                for a1, _ in clause1:
                                    if a1 != a and a1 not in learn_variables_list:
                                        learn_variables_list.append(a1)
                                learn_variables_list.remove(a)
                                process.append([a, implication_graph[a][3]])
                                break     

                clauses_sourse.append(process)
                learn_clause = []
                max_level = 0
                num_new = len(learn_CNF) + L
                for a in learn_variables_list:
                    learn_clause.append((a, not implication_graph[a][1]))
                    buc[a].append(num_new)
                    max_level = max(implication_graph[a][2], max_level)
                learn_CNF.append(learn_clause)

                #backtrack
                if len(learn_clause) == 1:
                    while True:
                        x, [x_if_assigned, x_value, x_assertion_level, _] = implication_graph.popitem() 
                        if x_if_assigned and x_assertion_level == 1:
                            break
                    assertion_level = 0
                    implication_graph[x] = [False, not x_value, assertion_level, num_new]
                    affect_clauses = buc[x]
                    return
                
                else:
                    while True:

                        
                        x, [x_if_assigned, _, x_assertion_level, _] = implication_graph.popitem()
                        if x_if_assigned and x_assertion_level == max_level:
                            break
                    affect_clauses = [num_new]
                    assertion_level = max_level
                    return

            elif check == None:
                continue

            else:
                unit_variable, unit_value = check
                if not unit_variable in implication_graph:
                    implication_graph[unit_variable] = [False, unit_value, assertion_level, num_c]
                    if assertion_level == 0:
                        learn_CNF.append([(unit_variable, unit_value)])
                        process = [num_c]
                        for a, _ in clause:
                            if a!= unit_variable:
                                process.append([a, implication_graph[a][3]])
                        clauses_sourse.append(process)
                        num_newclause = L - 1 + len(learn_CNF)
                        buc[unit_variable].append(num_newclause)
                        implication_graph[unit_variable][3] = num_newclause
                    for num in buc[unit_variable]:
                        if num not in affect_clauses_new:
                            affect_clauses_new.append(num)
        affect_clauses = affect_clauses_new
        return
    
    while flag:
        operate()

    return if_SAT, learn_CNF, implication_graph, clauses_sourse

def check_clause(clause, implication_graph):
    """Check the clause

        If the clause infers contradiction, return False
        
        If all literals but one are assigned value 0, use unit resolution, return the valuable and it's assignment
        
        Else, we can't get anything useful from this clause, return None

    """
    num_unassigned = 0
    clause_value = 0
    unit_variable, unit_value = None, None
    for a, b in clause:
        if a in implication_graph:
            if b == implication_graph[a][1]:
                clause_value = 1

        if not a in implication_graph:
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

def proof_process(cnf):
    """ Giving each step of the deduction by using resolution"""

    def str_of_literal(a, b):
        # Change [('x', False)] to ~x, change [('x', True)] to x.
        if not b:
            return '~' + a
        else:
            return a

    def display_clause(clause):
        # Turn clause to string by adding (,|,)
        if clause == []:
            return "empty clause"
        return ' | '.join(str_of_literal(a, b) for a, b in clause)
    
    
    
    L = len(cnf)
    if_SAT, learn_CNF, implication_graph, clauses_sourse = solve_cnf1(cnf)

    def find_clause(num):
        nonlocal L, cnf, learn_CNF
        if num <= L - 1:
            return cnf[num]
        else:
            return learn_CNF[num - L]

    def resolvent(clause1, clause2, x):
        clause_new = []
        if (x, True) in clause1 and (x, False) in clause2:
            for a1, b1 in clause1:
                if (a1, b1) != (x, True) and (a1, b1) not in clause_new:
                    clause_new.append((a1,b1))
            for a2, b2 in clause2:
                if (a2, b2) != (x, False) and (a2, b2) not in clause_new:
                    clause_new.append((a2, b2))
        elif (x, False) in clause1 and (x, True) in clause2:
            for a1, b1 in clause1:
                if (a1, b1) != (x, False) and (a1, b1) not in clause_new:
                    clause_new.append((a1,b1))
            for a2, b2 in clause2:
                if (a2, b2) != (x, True) and (a2, b2) not in clause_new:
                    clause_new.append((a2, b2))    
        else:
            return 'cannot use resolvent' 
        return clause_new

    if cnf == []:
        print("the cnf is an empty set")
        print()
        print("the cnf is satisfiable")
        return

    if any(len(clause) == 0 for clause in cnf):
        print("the clause " + str(implication_graph[None][3] + 1) + " is an empty clause")
        print()
        print("the cnf is unsatisfiable")
        return

    print("original CNF is:") 
    print(display_cnf(cnf))
    print()
    
    if if_SAT:
        print("the satisfying assignment is:")
        print(dict((x, implication_graph[x][1]) for x in implication_graph))
        print()
        print("the cnf is satisfiable")
        return
    
    for num_cl, cl_sourse in enumerate(clauses_sourse):
        for num_r, cl in enumerate(cl_sourse):
            if num_r == 0:
                clause1_num = cl
                clause1 = find_clause(clause1_num)
                print("clause " + str(clause1_num + 1) + " is:")
                print(display_clause(clause1))
            else:
                [x, clause2_num] = cl
                clause2 = find_clause(clause2_num)
                print("clause " + str(clause2_num + 1) + " is:")
                print(display_clause(clause2))
                clause1 = resolvent(clause1, clause2, x)
                print("do resolvent with " + x + ", got:")
                print(display_clause(clause1))
        if num_cl != len(clauses_sourse) - 1:
            if clause1 != []:
                print("so we learn clause " + str(num_cl + L +1) + " :")
                print(display_clause(clause1))
                print()

        else:
            print("it infers a controdiction")
            print()
            print("the cnf is unsatisfiable")
            return