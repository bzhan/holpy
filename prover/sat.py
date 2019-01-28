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
    print('hello,world')

def is_solution(cnf, inst):
    """Determines whether the given instantiation is a solution to
    the CNF.
    
    inst is a dictionary representing the satisfying assignment. It
    must contain assignment for all variables.
    
    Raises SATSolverException if inst does not contain assignment
    for some variable.
    
    """
    pass

def solve_cnf(cnf):
    """Solve the given CNF.
    
    If the CNF is satisfiable, returns the satisfying assignment
    as a dictionary.
    
    Otherwise, return None.
    
    """
    pass
