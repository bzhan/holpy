"""
Script for running a folder of smt files as well as store the stastics in a .csv file.

Usage: python -m stat FOLDER_NAME
"""
import time
import os
import sys
import csv
import concurrent.futures
from itertools import repeat

from smt.veriT import interface, proof_rec, proof_parser
from syntax.settings import settings
settings.unicode = False

smtlib_path = None

try:
    with open('smt/veriT/tests/smtlib_path.txt', 'r') as f:
        smtlib_path = f.readline().strip()
except FileNotFoundError:
    print("File smtlib_path.txt should be present in the smt/veriT/tests/ directory,")
    print("containing the path to the smtlib folder.")

import signal

class TO:
    def __init__(self, seconds=1, error_message='Timeout'):
        self.seconds = seconds
        self.error_message = error_message
    def handle_timeout(self, signum, frame):
        raise TimeoutError(self.error_message)
    def __enter__(self):
        signal.signal(signal.SIGALRM, self.handle_timeout)
        signal.alarm(self.seconds)
    def __exit__(self, type, value, traceback):
        signal.alarm(0)


try:
    with open('smt/veriT/tests/smtlib_path.txt', 'r') as f:
        smtlib_path = f.readline().strip()
except FileNotFoundError:
    print("File smtlib_path.txt should be present in the smt/veriT/tests/ directory,")
    print("containing the path to the smtlib folder.")

def test_parse_step(verit_proof, ctx):
    parser = proof_parser.proof_parser(ctx)
    steps = []
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        steps.append(parser.parse(s))

    return steps

def test_file(filename, show_time=True, test_eval=False, test_proofterm=False,
              step_limit=None, omit_proofterm=None, solve_timeout=10, eval_timeout=60):
    """Test a given file under eval or proofterm mode."""
    stastic = []
    global smtlib_path
    if not smtlib_path:
        return

    if filename[-4:] != 'smt2':
        return
    stastic.append(filename)
    abs_name = smtlib_path + filename
    if not interface.is_unsat(abs_name, timeout=solve_timeout):
        return [filename, 'TO', 'TO', 'TO']
    print(repr(filename) + ',')

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(abs_name, timeout=solve_timeout)
    if verit_proof is None:
        return [filename, 'TO', 'TO', 'TO']
    ctx = proof_rec.bind_var(abs_name)
    solve_time = time.perf_counter() - start_time
    solve_time_str = "%.3f" % solve_time

    # Parse
    start_time = time.perf_counter()
    steps = test_parse_step(verit_proof, ctx)
    parse_time = time.perf_counter() - start_time
    parse_time_str = "%.3f" % parse_time

    # Validation by macro.eval
    eval_time_str = ""
    if test_eval:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps)
        try:
            with TO(seconds=eval_timeout):
                pt = recon.validate(is_eval=True, step_limit=step_limit, omit_proofterm=omit_proofterm)
        except TimeoutError:
            return [filename, solve_time_str, parse_time_str, 'TO']
        eval_time = time.perf_counter() - start_time
        eval_time_str = "Eval: %.3f." % eval_time
        assert pt.rule != "sorry"

    if not test_proofterm:
        return [filename, solve_time_str, parse_time_str, eval_time_str]

    # Validation by macro.get_proof_term
    proofterm_time_str = ""
    if test_proofterm:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps)
        pt = recon.validate(is_eval=False, step_limit=step_limit, omit_proofterm=omit_proofterm)
        proofterm_time = time.perf_counter() - start_time
        proofterm_time_str = "Proofterm: %.3f." % proofterm_time
        assert pt.rule != "sorry"

    # Optional: print time
    if show_time:
        print("Solve: %.3f. Parse: %.3f. %s %s"
                    % (solve_time, parse_time, eval_time_str, proofterm_time_str))
    

def test_path(path, show_time=True, test_eval=False, test_proofterm=False,
              step_limit=None, omit_proofterm=None, solve_timeout=10, eval_timeout=120):
    """Test a directory containing SMT files.
    
    test_eval : bool - test evaluation of steps.
    test_proofterm : bool - test proof term reconstruction of steps.
    step_limit : [None, int] - limit on number of steps to test for each file.
    omit_proofterm : List[str] - list of macro names for which proof term reconstruction
        is omitted (evaluation is used instead).
        
    """
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path

    stats = []

    if not os.path.exists(abs_path):
        print("Directory %s not found." % path)
        return

    # if os.path.isdir(abs_path):
        # Input is a directory
    sub_paths = [path + '/' + child for child in os.listdir(abs_path)]
    # Check if abs_path is the lowest subpath
    if all(not os.path.isdir(sub_path) for sub_path in sub_paths):
        with concurrent.futures.ProcessPoolExecutor() as executor:
            res = list(executor.map(test_file, sub_paths, repeat(show_time),\
                        repeat(test_eval)))
            return res
    else:
        for sub_path in sub_paths:
            stats += test_path(sub_path, show_time=show_time, test_eval=test_eval, test_proofterm=test_proofterm,
                    step_limit=step_limit, omit_proofterm=omit_proofterm)
        return stats

# Parameters
# 1. folder name
# 2. verit solve timeout (default: 10s)
# 3. eval timeout (default: 180s)
if __name__ == "__main__":
    folder_name = str(sys.argv[1])
    solve_timeout = 10
    eval_timeout  = 120
    if len(sys.argv) == 3:
        solve_timeout = int(sys.argv[2])
    elif len(sys.argv) == 4:
        solve_timeout = int(sys.argv[2])
        eval_timeout  = int(sys.argv[3])
    
    stats = test_path(folder_name, test_eval=True, solve_timeout=solve_timeout, eval_timeout=eval_timeout)
    print("stats", stats)

    if not os.path.isdir('./smt/veriT/stastics'):
        os.mkdir('./smt/veriT/stastics')

    csv_name = folder_name.split("/")[-1]
    headers = ['filename', 'Solve', 'Parse', 'Eval']
    with open('./smt/veriT/stastics/%s.csv' % csv_name, 'w') as f:
        f_csv = csv.writer(f)
        f_csv.writerow(headers)
        f_csv.writerows(stats)