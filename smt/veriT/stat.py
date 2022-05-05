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
from smt.veriT.verit_macro import VeriTException
from syntax.settings import settings
settings.unicode = False

sys.setrecursionlimit(5000)

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
    unsat, res = interface.is_unsat(filename, timeout=solve_timeout)
    if not unsat:
        return [filename, str(res), '', '', '']
    print(repr(filename) + ',')

    assts = proof_rec.get_assertions(filename)

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(filename, timeout=solve_timeout)
    if verit_proof is None:
        return [filename, 'NO PROOF (veriT)', '', '', '']
    ctx = proof_rec.bind_var(filename)
    solve_time = time.perf_counter() - start_time
    solve_time_str = "%.3f" % solve_time

    # Parse
    start_time = time.perf_counter()
    try:
        steps = test_parse_step(verit_proof, ctx)
    except Exception as e:
        return [filename, solve_time_str, 'PARSING ERROR (HolPy) %s' % e, '', '']
    parse_time = time.perf_counter() - start_time
    parse_time_str = "%.3f" % parse_time    

    # Validation by macro.eval
    eval_time_str = ""
    if test_eval:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)
        try:
            with TO(seconds=eval_timeout):
                try:
                    pt = recon.validate(is_eval=True, step_limit=step_limit, omit_proofterm=omit_proofterm, with_bar=False)
                except Exception as e:
                    return  [filename, solve_time_str, parse_time_str, 'Filename: %s Error: %s' % (str(filename), str(e)), len(steps)]                   
        except TimeoutError:
            return [filename, solve_time_str, parse_time_str, 'Proof evaluation is timeout! (HolPy)', len(steps)]
        eval_time = time.perf_counter() - start_time
        eval_time_str = "Eval: %.3f" % eval_time
        assert pt.rule != "sorry"

    if not test_proofterm:
        return [filename, solve_time_str, parse_time_str, eval_time_str, len(steps)]

    # Validation by macro.get_proof_term
    proofterm_time_str = ""
    if test_proofterm:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)
        try:
            with TO(seconds=eval_timeout):
                try:
                    pt = recon.validate(is_eval=False, step_limit=step_limit, omit_proofterm=omit_proofterm, with_bar=False)
                except Exception as e:
                    return [filename, solve_time_str, parse_time_str, 'Error: %s %s' % (str(filename), str(e)), len(steps)]
        except TimeoutError:
            return [filename, solve_time_str, parse_time_str, 'Proof reconstruction is timeout! (HolPy)', len(steps)]
        proofterm_time = time.perf_counter() - start_time
        proofterm_time_str = "Proofterm: %.3f" % proofterm_time
        assert pt.rule != "sorry"

    if test_proofterm:
        return [filename, solve_time_str, parse_time_str, proofterm_time_str, len(steps)]

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

    _, file_names = run_fast_scandir(abs_path, ['.smt2'])

    with concurrent.futures.ProcessPoolExecutor(max_workers=os.cpu_count()) as executor:
        res = executor.map(test_file, file_names, repeat(show_time),
                        repeat(test_eval), repeat(test_proofterm), repeat(step_limit),
                            repeat(omit_proofterm), repeat(solve_timeout), repeat(eval_timeout))
    return res

def run_fast_scandir(dir, ext):    # dir: str, ext: list
    subfolders, files = [], []

    for f in os.scandir(dir):
        if f.is_dir():
            subfolders.append(f.path)
        if f.is_file():
            if os.path.splitext(f.name)[1].lower() in ext:
                files.append(f.path)


    for dir in list(subfolders):
        sf, f = run_fast_scandir(dir, ext)
        subfolders.extend(sf)
        files.extend(f)
    return subfolders, files

# Parameters
# 1. folder name
# 2. eval (--eval) or get_proof_term (--proofterm)
# 2. verit solve timeout (default: 10s)
# 3. eval timeout (default: 180s)
if __name__ == "__main__":
    folder_name = str(sys.argv[1])
    solve_timeout = 120
    eval_timeout  = 300
    test_eval = True # test eval as default, test proofterm if it is false
    if len(sys.argv) == 3:
        if sys.argv[2] == "--proofterm":
            test_eval = False
        elif sys.argv[2] == "--eval":
            test_eval = True
        
    if len(sys.argv) == 4:
        solve_timeout = int(sys.argv[3])
    elif len(sys.argv) == 5:
        solve_timeout = int(sys.argv[3])
        eval_timeout  = int(sys.argv[4])
    
    start_time = time.perf_counter()
    if test_eval:
        stats = test_path(folder_name, test_eval=True, test_proofterm=False, solve_timeout=solve_timeout, eval_timeout=eval_timeout, omit_proofterm=['th_resolution'])
    else:
        stats = test_path(folder_name, test_eval=False, test_proofterm=True, solve_timeout=solve_timeout, eval_timeout=eval_timeout, omit_proofterm=['th_resolution'])
    print("stats", stats)
    end_time = time.perf_counter()
    if not os.path.isdir('./smt/veriT/stastics'):
        os.mkdir('./smt/veriT/stastics')
    if not os.path.isdir('./smt/veriT/stastics/eval'):
        os.mkdir('./smt/veriT/stastics/eval')
    if not os.path.isdir('./smt/veriT/stastics/proofterm'):
        os.mkdir('./smt/veriT/stastics/proofterm')
    
    

    csv_name = folder_name.replace('/', '.')
    if test_eval:
        headers = ['filename', 'Solve', 'Parse', 'Eval', 'Steps']
        res_file_name = './smt/veriT/stastics/eval/%s.csv' % csv_name
    else:
        headers = ['filename', 'Solve', 'Parse', 'ProofTerm', 'Steps']
        res_file_name = './smt/veriT/stastics/proofterm/%s.csv' % csv_name

    with open(res_file_name, 'w') as f:
        f_csv = csv.writer(f)
        f_csv.writerow(headers)
        f_csv.writerows(stats)
        f_csv.writerow(["Total time: %.3f" % (end_time - start_time)])