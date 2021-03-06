"""
VeriT Interface.
"""

import z3
import subprocess
from prover import z3wrapper
from smt.veriT import parser, proof
from sys import platform
import time

class SATException(Exception):
    """Exception for SAT term."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

def solve(f):
    """Use veriT solver to solve a smt2 file"""
    args = "--proof-prune "\
            "--proof-with-sharing "\
            "--proof-merge "\
            "--disable-print-success "\
            "--disable-banner "\
            "--proof-version=2 "\
            "--proof=-"

    if platform == "win32":
        p = subprocess.Popen("veriT %s %s" % (args, f), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    else:
        p = subprocess.Popen("veriT %s %s" % (args, f), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            shell=True)

    output, err = p.communicate()
    print(output.decode("utf-8"))
    return output.decode("utf-8")
    

def solve_and_proof(tm):
    """Use veriT to determine whether a logical term is satisfiable."""
    s = z3wrapper.solve_core(z3.Solver(ctx=z3.Context()) ,tm, False)
    with open("proof.smt2", "a") as f:
        f.seek(0)
        f.truncate()
        f.write("(set-logic LRA)\n" + s.to_smt2())

    proof_rec("proof.smt2")

def proof_rec(file_name):
    """Given a smt2 file, get the proof and reconstruct it."""
    res = solve(file_name).split("\n")
    if res[0] in ("sat", "unsat", "unknown"):
        status, proof_steps = res[0], res[1:-1]
    elif res[0] == "unsupported":
        status, proof_steps = res[1], res[2:-1]
    else:
        raise NotImplementedError
    if status in ("sat", "unknown"):
        print(status)
        return

    ctx = parser.bind_var(file_name)
    proof_parser = parser.term_parser(ctx)
    parsed_proof_steps = [proof_parser.parse(step) for step in proof_steps]
    rct = proof.ProofReconstruction(parsed_proof_steps)
    time1 = time.perf_counter()
    hol_proof = rct.main()
    time2 = time.perf_counter()
    print("total time: ", time2 - time1)
    return hol_proof