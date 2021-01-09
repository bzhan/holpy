"""
VeriT Interface.
"""

import z3
import subprocess
from prover import z3wrapper

class SATException(Exception):
    """Exception for SAT term."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

def solve(f):
    """Use veriT solver to solve a smt2 file"""
    p = subprocess.Popen("veriT.exe --proof-prune \
                        --proof-with-sharing \
                        --proof-merge \
                        --disable-print-success \
                        --disable-banner \
                        --proof-version=2 \
                        --proof=- %s" % f, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, err = p.communicate()
    print(">>>")
    print(output.decode("utf-8"))
    # print(err)
    return output.decode("utf-8")
    

def solve_and_proof(tm):
    """Use veriT to determine whether a logical term is satisfiable."""
    s = z3wrapper.solve_core(z3.Solver(ctx=z3.Context()) ,tm, False)
    with open("proof.smt2", "a") as f:
        f.seek(0)
        f.truncate()
        f.write("(set-logic LRA)\n" + s.to_smt2())

    result = solve("proof.smt2").split("\n")
    if result[0] == "sat":
        raise SATException(str(tm))
    elif result[0] == "unsat":
        return result[1:]
    else:
        raise NotImplementedError



