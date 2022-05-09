"""
VeriT Interface.
"""

import z3
import subprocess
from prover import z3wrapper
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
            proof = output.decode('UTF-8')
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
                print("Proof extraction from veriT is timeout (veriT)")
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
    return "Proof extraction from veriT is timeout (veriT)"
 
def is_unsat(f, timeout=10) -> tuple:
    """Given a smt2 file, use verit to solve it and return True if it is UNSAT."""
    args = "--disable-print-success"
    res = check_sat_from_file(f)
    if res in ("sat", "unknown", "none"):
        return False, res
    with subprocess.Popen("veriT %s %s" % (args, f),
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
            output = output.decode('UTF-8').split("\n")
            if output == [""]:
                return False, "unknown"
            res = output[1].strip()
            return False if res in ("sat", "unknown", "unsupported") else True, res
        except subprocess.TimeoutExpired:
            # Kill process
            if os.name == "nt": # Windows
                subprocess.call(['taskkill', '/F', '/T', '/PID', str(p.pid)])
                return False, "UNSAT checking is timeout! (veriT)"
            else: # Linux
                p.terminate()
                p.wait()
                p.kill()
                print("UNSAT checking is timeout! (veriT)")
                return False, "UNSAT checking is timeout! (veriT)"

