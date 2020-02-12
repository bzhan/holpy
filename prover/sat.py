from copy import copy

"""
Implementation of SAT solver.

CNFs are represented using lists of lists of literals, where
each literal is given by a pair (x, b), where x is a string
(name of the boolean variable), and b is a boolean value giving
the sign of the literal.

For example, (~x | y) & (~y | z) is represented as
[[('x', False), ('y', True)], [('y', False), ('z', True)]].

"""


def str_of_literal(lit):
    return lit[0] if lit[1] else '¬' + lit[0]

def str_of_clause(clause):
    if len(clause) == 0:
        return 'False'
    else:
        return ' ∨ '.join(str_of_literal(lit) for lit in clause)

def str_of_cnf(cnf):
    if len(cnf) == 0:
        return 'True'
    else:
        return ' ∧ '.join('(' + str_of_clause(clause) + ')' for clause in cnf)

def resolution(clause1, clause2, name):
    """Apply resolution to the two clauses on the given name.

    Returns the new clause. This function assumes the inputs are valid.

    """
    lit1 = [lit for lit in clause1 if lit[0] != name]
    lit2 = [lit for lit in clause2 if lit[0] != name]
    return list(set(lit1 + lit2))

def is_solution(cnf, assignment):
    """Test whether the given assignment is a solution to the CNF.

    assignment is a dictionary from variable names to truth values.
    It is not required that all variables in the CNF are assigned.

    """
    for clause in cnf:
        satisfied = False
        for lit in clause:
            name, val = lit
            if name in assignment and val == assignment[name]:
                satisfied = True
                break
        if not satisfied:
            return False
    return True

def solve_cnf(cnf, *, debug=False):
    cnf = copy(cnf)  # avoid modifying the input
    assigns = dict()
    level = 0
    proofs = dict()
    
    def print_debug(s):
        if debug:
            print(s)

    def unit_propagate():
        while True:
            has_unsatisfied = False  # whether there is still clause to be satisfied
            has_propagate = False  # whether a propagation has occurred
            for clause_id, clause in enumerate(cnf):
                satisfied = False  # whether the current clause is satisfied
                unassigned = []  # list of unassigned literals

                # Iterate over the literals, check if the existing assignment satisfies
                # the clause, and if not, what are the unassigned literals.
                for lit in clause:
                    name, val = lit
                    if name in assigns:
                        if val == assigns[name][0]:
                            satisfied = True
                            break
                    else:
                        unassigned.append(lit)

                # If the clause is not already satisfied, no unassigned literals implies
                # conflict. One unassigned literals implies possibility for unit propagation.
                if not satisfied:
                    if len(unassigned) == 0:
                        return 'conflict', clause_id
                    elif len(unassigned) == 1:
                        name, val = unassigned[0]
                        print_debug('Unit propagate %s = %s using clause %s' % (name, val, clause_id))
                        assigns[name] = (val, False, level, clause_id)
                        has_propagate = True
                        break
                    else:
                        has_unsatisfied = True

            if not has_propagate:
                if not has_unsatisfied:
                    return 'satisfiable'
                else:
                    return None

    def analyze_conflict(clause_id):
        clause = cnf[clause_id]
        proof = [clause_id]
        print_debug('Analyze conflict on clause %s: %s' % (clause_id, str_of_clause(clause)))
        while True:
            has_resolution = False
            for lit in clause:
                name, val = lit
                assert name in assigns and val != assigns[name][0]
                _, is_decide, level, propagate_id = assigns[name]
                if not is_decide:
                    has_resolution = True
                    proof.append(propagate_id)
                    clause = resolution(clause, cnf[propagate_id], name)
                    print_debug('Resolution with clause %s on atom %s, obtaining %s' % (propagate_id, name, str_of_clause(clause)))
                    break

            if not has_resolution:
                break

        return proof, clause
    
    
    def backtrack(clause_id):
        # Analyze conflict, record the new clause and its proof
        proof, clause = analyze_conflict(clause_id)
        new_id = len(cnf)
        cnf.append(clause)
        proofs[new_id] = proof

        # Sort the clause by level, find the second to last level
        if len(clause) == 0:
            return 'unsatisfiable'
        elif len(clause) == 1:
            backtrack_level = 0
        else:
            clause = sorted(clause, key=lambda lit: assigns[lit[0]][2])
            name, _ = clause[-2]
            backtrack_level = assigns[name][2]

        # Backtrack to that level
        assigned_names = list(assigns.keys())
        for name in assigned_names:
            if assigns[name][2] > backtrack_level:
                del assigns[name]

        return backtrack_level
    
    # Find set of all variables
    variables = set()
    for clause in cnf:
        for name, _ in clause:
            variables.add(name)

    propagate_res = unit_propagate()
    while True:
        if propagate_res == 'satisfiable':
            # Formula is satisfiable, return only assigned values
            assignment = dict((name, val) for name, (val, _, _, _) in assigns.items())
            return 'satisfiable', assignment
        elif propagate_res is None:
            # Unit propagation stops, choose a new variable
            level += 1
            for var in variables:
                if var not in assigns:
                    assigns[var] = (True, True, level, None)
                    break
        else:
            # Conflict occurs, backtrack
            _, clause_id = propagate_res
            backtrack_res = backtrack(clause_id)
            if backtrack_res == 'unsatisfiable':
                # Formula is unsatisfiable, return the proof
                return 'unsatisfiable', proofs
            else:
                level = backtrack_res
            
        propagate_res = unit_propagate()
