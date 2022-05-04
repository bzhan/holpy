"""
VeriT Interface.
"""

import z3
import subprocess
from prover import z3wrapper
from smt.veriT import parser, proof
import os
import time

class SATException(Exception):
    """Exception for SAT term."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

def solve(f, write_file=False, timeout=5):
    """Use veriT solver to solve a smt2 file"""
    args = "--proof-prune "\
            "--proof-with-sharing "\
            "--proof-merge "\
            "--disable-print-success "\
            "--disable-banner "\
            "--proof=-"

    with subprocess.Popen("veriT %s %s" % (args, f),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
            if output == b'':
                return None
            proof = output.decode('utf-8')
            if write_file:
                with open("proof.txt", "w") as f:
                    f.write(proof)
            return proof
        except subprocess.TimeoutExpired:
            # Kill process
            if os.name == "nt": # Windows
                subprocess.call(['taskkill', '/F', '/T', '/PID', str(p.pid)])
                return None
            else: # Linux
                p.terminate()
                p.wait()
                p.kill()
                print("Proof extraction from veriT is timeout")
                return None

def check_sat_from_file(filename: str) -> str:
    """check the status from smt file"""
    with open(filename, "r") as f:
        for line in f.readlines():
            if line == "(set-info :status sat)":
                return "sat"
            elif line == "(set-info :status unknown)":
                return "unknown"
            elif line == "(set-info :status unsat)":
                return "unsat"
            elif line.startswith("(declare"):
                break
    return "none"
 
def is_unsat(f, timeout=10):
    """Given a smt2 file, use verit to solve it and return True if it is UNSAT."""
    args = "--disable-print-success"
    res = check_sat_from_file(f)
    if res in ("sat", "unknown"):
        return False, res
    with subprocess.Popen("veriT %s %s" % (args, f),
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
            res = output.decode('UTF-8').split("\n")[1].strip()
            return False if res in ("sat", "unknown", "unsupported") else True, res
        except subprocess.TimeoutExpired:
            # Kill process
            if os.name == "nt": # Windows
                subprocess.call(['taskkill', '/F', '/T', '/PID', str(p.pid)])
                return False
            else: # Linux
                p.terminate()
                p.wait()
                p.kill()
                print("UNSAT checking is timeout!")
                return False, "UNSAT checking is timeout!"

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
    res = solve(file_name).replace("\r", "").split("\n")
    ctx = proof_parser.bind_var(file_name)
    proof_parser = parser.term_parser(ctx)
    steps = []
    for step in res:
        if step in ("sat", "unknown", "unsupported", "unsat"):
            continue
        steps.append(proof_parser.parse(step))
