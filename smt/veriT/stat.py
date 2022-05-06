"""
Script for running a folder of smt files as well as store the stastics in a .csv file.

Usage: python -m stat FOLDER_NAME
"""
import time
from datetime import datetime
import os
import sys
import csv
import concurrent.futures
from itertools import repeat
import shutil
import subprocess

from smt.veriT import interface, proof_rec, proof_parser
from smt.veriT.verit_macro import VeriTException
from syntax.settings import settings
settings.unicode = False

sys.setrecursionlimit(10000)

smtlib_path = None

try:
    with open('smt/veriT/tests/smtlib_path.txt', 'r') as f:
        smtlib_path = f.readline().strip()
except FileNotFoundError:
    print("File smtlib_path.txt should be present in the smt/veriT/tests/ directory,")
    print("containing the path to the smtlib folder.")

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

    return steps, len(steps)


def test_proof(filename, solve_timeout=120):
    """note: sys.getsizeof(verit_proof) failed in pypy3, so we can't get the proof size now"""
    print(filename)
    unsat, res = interface.is_unsat(filename, timeout=solve_timeout)
    if not unsat:
        return [filename[11:], 'UN-UNSAT']
    verit_proof = interface.solve(filename, timeout=solve_timeout)
    if verit_proof is None:
        return [filename[11:], 'NO PROOF']
    else:
        return [filename[11:], "RETURN PROOF"]

def remove_file(filename):
    if os.path.isfile(filename):
        try:
            os.remove(filename)
        except FileNotFoundError:
            return

def test_file(filename, show_time=True, test_eval=False, test_proofterm=False,
              step_limit=None, omit_proofterm=None, solve_timeout=120, eval_timeout=300):
    """Test a given file under eval or proofterm mode."""

    global smtlib_path
    if not smtlib_path:
        return

    if filename[-4:] != 'smt2':
        return

    unsat, res = interface.is_unsat(filename, timeout=solve_timeout)
    if not unsat:
        return [filename, str(res), '', '', '']
    print(repr(filename) + ',')

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(filename, timeout=solve_timeout)
    if verit_proof is None:
        print([filename, 'NO PROOF (veriT)', '', '', ''])
        return [filename, 'NO PROOF (veriT)', '', '', '']    

    solve_time = time.perf_counter() - start_time
    solve_time_str = "%.3f" % solve_time

    # write proof to a file
    if not os.path.isdir("./smt/veriT/proof"):
        os.mkdir("./smt/veriT/proof")

    proof_file_name = "./smt/veriT/proof/%s" % (filename.replace("/", "."))
    with open(proof_file_name, "w") as f:
        f.write(verit_proof)

    try:
        with subprocess.Popen("pypy3 -m smt.veriT.stastics.validate_file '%s' \"%s\" '%s'" % (filename, proof_file_name, str(test_eval)), 
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True) as p:
            try:
                output,err_message = p.communicate(timeout=eval_timeout)
                output = output.decode('UTF-8')
                # print("output", repr(output))
                if err_message != b'':
                    print("error", err_message)
                print("output", [p for p in output[:-2].split(",")])
                remove_file(proof_file_name)
                return [p for p in output[:-2].split(",")]
            except subprocess.TimeoutExpired:
                # Kill process
                if os.name == "nt": # Windows
                    subprocess.call(['taskkill', '/F', '/T', '/PID', str(p.pid)])
                    return [filename, solve_time_str, 'TIMEOUT', 'TIMEOUT', step_size]
                else: # Linux
                    p.terminate()
                    p.wait()
                    p.kill()
                    print([filename, solve_time_str, 'TIMEOUT', 'TIMEOUT', ''])
                    remove_file(proof_file_name)
                    return [filename, solve_time_str, 'TIMEOUT', 'TIMEOUT', '']
    except OSError:
        print("pypy3 -m smt.veriT.stastics.validate_file '%s' '%s' 'false'" % (filename, verit_proof))
        return [filename, solve_time_str, 'OS ERROR', 'OS_ERROR', '']

def test_path(path, show_time=True, test_eval=False, test_proofterm=False,
              step_limit=None, omit_proofterm=None, solve_timeout=120, eval_timeout=300, test_full=False):
    """Test a directory containing SMT files.
    
    test_eval : bool - test evaluation of steps.
    test_proofterm : bool - test proof term reconstruction of steps.
    step_limit : [None, int] - limit on number of steps to test for each file.
    omit_proofterm : List[str] - list of macro names for which proof term reconstruction
        is omitted (evaluation is used instead).
    test_full: bool - whether test all smt2 files
    """
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path

    stats = []

    if not os.path.exists(abs_path):
        print("Directory %s not found." % path)
        return

    file_names = []
    if test_full:
        print("test full")
        with open("./smt/veriT/data/test_files.txt") as f:
            file_names = [smtlib_path+file_name[:-1] for file_name in f.readlines()]
            # print(file_names)
    elif os.path.isfile("./smt/veriT/data/%s.csv" % path):
        with open("./smt/veriT/data/%s.csv" % path) as f:
            f_csv = csv.reader(f)
            _ = next(f_csv)
            for row in f_csv:
                if len(row) == 2 and "RETURN PROOF" == row[-1]:
                    file_names.append(smtlib_path+row[0])
    else:
        _, file_names = run_fast_scandir(abs_path, ['.smt2'])
    if len(file_names) > os.cpu_count():
        max_workers = os.cpu_count()
    else:
        max_workers = len(file_names)
    if max_workers == 0:
        max_workers = 1
    print("start at %s" %  datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
    print("file numbers", len(file_names))
    with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
        res = executor.map(test_file, file_names, repeat(show_time),
                        repeat(test_eval), repeat(test_proofterm), repeat(step_limit),
                            repeat(omit_proofterm), repeat(solve_timeout), repeat(eval_timeout))
    print("end")
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

def test_path_proof(path, solve_timeout=120):
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path

    stats = []

    if not os.path.exists(abs_path):
        print("Directory %s not found." % path)
        return

    _, file_names = run_fast_scandir(abs_path, ['.smt2'])
    time1 = time.perf_counter()
    if len(file_names) > os.cpu_count():
        max_workers = os.cpu_count()
    else:
        max_workers = len(file_names)
    with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
        res = executor.map(test_proof, file_names, repeat(solve_timeout))
    time2 = time.perf_counter()
    csv_name = path.replace('/', '.')
    if not os.path.isdir("./smt/veriT/data"):
        os.mkdir("./smt/veriT/data")
    file_name = "./smt/veriT/data/%s.csv" % csv_name
    with open(file_name, 'w') as f:
        f_csv = csv.writer(f)
        f_csv.writerow(['FILENAME', 'STATUS'])
        f_csv.writerows(res)
        f_csv.writerow(["TOTAL TIME %.3f" % (time2 - time1)])
        f_csv.writerow(["TIMESTAMP %s" % datetime.now().strftime('%Y-%m-%d %H:%M:%S')])
    return res

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
    find_proof = False
    test_full = False
    if len(sys.argv) == 3:
        if sys.argv[2] == "--proofterm":
            test_eval = False
        elif sys.argv[2] == "--eval":
            test_eval = True
        elif sys.argv[2] == "--find-proof":
            find_proof = True
    if folder_name == "--full":
        test_full = True
        folder_name = "QF_UF"
    if find_proof:
        test_path_proof(folder_name, solve_timeout=120)
    else:
        if len(sys.argv) == 4:
            solve_timeout = int(sys.argv[3])
        elif len(sys.argv) == 5:
            solve_timeout = int(sys.argv[3])
            eval_timeout  = int(sys.argv[4])
        
        start_time = time.perf_counter()
        if test_eval:
            stats = test_path(folder_name, test_eval=True, test_proofterm=False, solve_timeout=solve_timeout, eval_timeout=eval_timeout, test_full=test_full)
        else:
            stats = test_path(folder_name, test_eval=False, test_proofterm=True, solve_timeout=solve_timeout, eval_timeout=eval_timeout, test_full=test_full)
        end_time = time.perf_counter()
        print("stats", stats)
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
        if test_full:
            if test_eval:
                res_file_name = './smt/veriT/stastics/eval/SMT.csv'
            else:
                res_file_name = './smt/veriT/stastics/proofterm/SMT.csv'

        with open(res_file_name, 'w') as f:
            f_csv = csv.writer(f)
            f_csv.writerow(headers)
            f_csv.writerows(stats)
            f_csv.writerow(["Total time: %.3f" % (end_time - start_time)])
            f_csv.writerow([datetime.now().strftime('%Y-%m-%d %H:%M:%S')])