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
import signal
import subprocess
from typing import Optional

from smt.veriT import proof_rec, proof_parser, command
from smt.veriT.verit_macro import VeriTException
from syntax.settings import settings
from kernel.report import ProofReport
settings.unicode = False

sys.setrecursionlimit(10000)


class TO:
    def __init__(self, seconds=1, error_message='Timeout'):
        if seconds <= 1:
            self.seconds =  1
        else:
            self.seconds = int(seconds)
        self.error_message = error_message
    def handle_timeout(self, signum, frame):
        raise TimeoutError(self.error_message)
    def __enter__(self):
        signal.signal(signal.SIGALRM, self.handle_timeout)
        signal.alarm(self.seconds)
    def __exit__(self, type, value, traceback):
        signal.alarm(0)

class TimeoutError(Exception):
    pass

def test_parse_step(verit_proof, ctx):
    parser = proof_parser.proof_parser(ctx)
    steps = []
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        step = parser.parse(s)
        if isinstance(step, command.Step) and step.rule_name == "lia_generic":
            return ["lia_generic"]
        steps.append(step)
    return steps

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

def solve(filename: str, timeout:int=120) -> Optional[str]:
    res = check_sat_from_file(filename)
    if res in ("sat", "unknown", "none"):
        return None
    args = "--proof-prune "\
            "--proof-with-sharing "\
            "--proof-merge "\
            "--disable-print-success "\
            "--disable-banner "\
            "--proof=-"

    with subprocess.Popen("veriT %s %s" % (args, filename),
                          stdout=subprocess.PIPE, 
                          stderr=subprocess.PIPE, shell=True, preexec_fn=os.setsid) as p:
        try:
            output, err_msg = p.communicate(timeout=timeout)
            output_lines = output.decode('UTF-8').split("\n")
            if output_lines == [""]:
                return None
            elif output_lines[1].strip() in ("sat", "unknown", "unsupported"):
                return None
            else:
                return output.decode('UTF-8')
        except subprocess.TimeoutExpired:
            # Kill processes
            print("Kill")
            os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            return None

def cvc5_solve(filename, timeout=120):
    res = check_sat_from_file(filename)
    if res in ("sat", "unknown", "none"):
        return None
    args =  "--dump-proofs "\
            "--proof-format-mode=alethe "\
            "--simplification=none "\
            "--dag-thresh=0 "\
            "--proof-granularity=theory-rewrite "
    
    with subprocess.Popen("cvc5 %s %s" % (args, filename),
                          stdout=subprocess.PIPE, 
                          stderr=subprocess.PIPE, shell=True, preexec_fn=os.setsid) as p:
        try:
            output, err_msg = p.communicate(timeout=timeout)
            # print(output)
            output_lines = output.decode('UTF-8').split("\n")
            if output_lines == [""]:
                return None
            elif output_lines[1].strip() in ("sat", "unknown", "unsupported"):
                return None
            else:
                return output.decode('UTF-8')
        except subprocess.TimeoutExpired:
            # Kill processes
            print("Kill")
            os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            return None

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

def test_file(filename, test_eval=False, test_proofterm=False,
              step_limit=None, omit_proofterm=None, solve_timeout=120, eval_timeout=300, test_expand=test_expand):
    """Test a given file under eval or proofterm mode."""
    if filename[-4:] != 'smt2':
        return
    # unsat, res = interface.is_unsat(filename, timeout=solve_timeout)
    # if not unsat:
    #     return [filename, str(res), '', '', '']

    # assts = proof_rec.get_assertions(filename) 

    print(repr(filename) + ',')
    # Solve
    start_time = time.perf_counter()
    verit_proof = solve(filename, timeout=solve_timeout)
    if verit_proof is None:
        print([filename, 'NO PROOF (veriT)', '', '', ''])
        return [filename, 'NO PROOF (veriT)', '', '', '']
    if verit_proof.strip() == "unknown":
        print("%s unknown proof" % filename)
        return [filename, 'UNKNOWN PROOF (veriT)', '', '', '']
    solve_time = time.perf_counter() - start_time
    solve_time_str = "%.3f" % solve_time

    # Parse
    start_time = time.perf_counter()
    try:
        with TO(seconds=60):
            try:
                ctx = proof_rec.bind_var(filename)
                steps = test_parse_step(verit_proof, ctx)
            except Exception as e:
                return [filename, solve_time_str, str(e), '', '']
    except Exception as e:
        return [filename, solve_time_str, str(e), '', '']
    parse_time_str = "%.3f" % (time.perf_counter() - start_time)
    
    # lia_generic is not supported
    if len(steps) == 1 and steps[0] == "lia_generic":
        return [filename, solve_time_str, 'lia_generic', '', '']
    
    # eval
    start_time = time.perf_counter()
    if test_eval:
        try:
            with TO(seconds=300):
                try:
                    recon = proof_rec.ProofReconstruction(steps)
                    pt = recon.validate(is_eval=True, step_limit=step_limit, omit_proofterm=omit_proofterm, with_bar=False)
                except Exception as e:
                    return [filename, solve_time_str, parse_time_str, str(e), len(steps)]
        except Exception as e:
            return [filename, solve_time_str, parse_time_str, str(e), len(steps)]
        eval_time_str = "%.3f" % (time.perf_counter() - start_time)
        return [filename, solve_time_str, parse_time_str, eval_time_str, len(steps)]
    # get_proof_term
    else:
        try:
            with TO(seconds=300):
                try:
                    recon = proof_rec.ProofReconstruction(steps)
                    if test_expand:
                        rpt = ProofReport()
                        pt = recon.validate(is_eval=False, step_limit=step_limit, omit_proofterm=omit_proofterm, with_bar=False, test_expand=test_expand, rpt=rpt)
                    else:
                        pt = recon.validate(is_eval=False, step_limit=step_limit, omit_proofterm=omit_proofterm, with_bar=False)
                except Exception as e:
                    end_time = time.perf_counter()
                    print([filename, solve_time_str, parse_time_str, "%s %.3f" % (str(e), end_time-start_time), len(steps)])
                    return [filename, solve_time_str, parse_time_str, "Exception: %s %.3f" % (str(e), end_time-start_time), len(steps)]
        except Exception as e:
            end_time = time.perf_counter()
            return [filename, solve_time_str, parse_time_str, "Exception: %s %.3f" % (str(e), end_time-start_time), len(steps)]
        proof_time_str = "%.3f" % (time.perf_counter() - start_time)
        print([filename, solve_time_str, parse_time_str, proof_time_str, len(steps)])
        return [filename, solve_time_str, parse_time_str, proof_time_str, len(steps)]

    
def test_path(path, show_time=True, test_eval=False, test_proofterm=False,
              step_limit=None, omit_proofterm=None, solve_timeout=10, eval_timeout=120, test_expand=False):
    """Test a directory containing SMT files.
    
    test_eval : bool - test evaluation of steps.
    test_proofterm : bool - test proof term reconstruction of steps.
    step_limit : [None, int] - limit on number of steps to test for each file.
    omit_proofterm : List[str] - list of macro names for which proof term reconstruction
        is omitted (evaluation is used instead).
        
    """
    smtlib_path = "../smt-lib/"

    abs_path = smtlib_path + path

    stats = []

    # if path != "" and not os.path.exists(abs_path):
    #     print("Directory %s not found." % path)
    #     return

    if path == "":
        print("test full")
        with open("./smt/veriT/data/test_files.txt") as f:
            file_names = [smtlib_path+file_name[:-1] for file_name in f.readlines()]
    elif os.path.isfile("./smt/veriT/data/%s.csv" % path):
        file_names = []
        with open("./smt/veriT/data/%s.csv" % path) as f:
            f_csv = csv.reader(f)
            headers = next(f_csv)
            for row in f_csv:
                if len(row) == 2 and "RETURN PROOF" == row[-1]:
                    file_names.append(smtlib_path+row[0])
    else:
        _, file_names = run_fast_scandir(abs_path, ['.smt2'])
    if len(file_names) > os.cpu_count():
        max_workers = os.cpu_count()
    else:
        max_workers = len(file_names)
    print("start at %s" %  datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
    with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
        res = executor.map(test_file, file_names,
                        repeat(test_eval), repeat(test_proofterm), repeat(step_limit),
                            repeat(omit_proofterm), repeat(solve_timeout), repeat(eval_timeout), repeat(test_expand))
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
    smtlib = "../smt-lib/"
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
    test_expand = False
    if len(sys.argv) == 3:
        if sys.argv[2] == "--proofterm":
            test_eval = False
        elif sys.argv[2] == "--eval":
            test_eval = True
        elif sys.argv[2] == "--find-proof":
            find_proof = True
        elif sys.argv[2] == "--test-expand":
            test_eval = False
            test_expand = True
    if sys.argv[1] == "--SMT-LIB":
        test_full = True
        assert len(sys.argv) == 3
        last_arg = sys.argv[-1]
        assert last_arg in ("--eval", "--proofterm")
        if last_arg == "--eval":
            test_eval = True
        else:
            test_eval = False
    print()
    for arg in sys.argv:
        print(arg)
    print("test_full %s" % test_full)
    print("folder")
    start_time = time.perf_counter()
    if find_proof:
        test_path_proof(folder_name, solve_timeout=120)
    elif test_full:
        stats = test_path("", test_eval=test_eval, test_proofterm=not test_eval, solve_timeout=solve_timeout, eval_timeout=eval_timeout)
    elif not test_full:
        if len(sys.argv) == 4:
            solve_timeout = int(sys.argv[3])
        elif len(sys.argv) == 5:
            solve_timeout = int(sys.argv[3])
            eval_timeout  = int(sys.argv[4])
        
        start_time = time.perf_counter()
        if test_eval:
            stats = test_path(folder_name, test_eval=True, test_proofterm=False, solve_timeout=solve_timeout, eval_timeout=eval_timeout, test_expand=test_expand)
        else:
            stats = test_path(folder_name, test_eval=False, test_proofterm=True, solve_timeout=solve_timeout, eval_timeout=eval_timeout, test_expand=test_expand)
    
    end_time = time.perf_counter()
    print("stats", stats)
    if not os.path.isdir('./smt/veriT/stastics'):
        os.mkdir('./smt/veriT/stastics')
    if test_eval and not os.path.isdir('./smt/veriT/stastics/eval'):
        os.mkdir('./smt/veriT/stastics/eval')
    if not test_eval and not os.path.isdir('./smt/veriT/stastics/proofterm'):
        os.mkdir('./smt/veriT/stastics/proofterm')
    
    if test_full:
        csv_name = "SMT-LIB"
    elif test_expand:
        csv_name = "SMT-LIB-Expand-Macro"
    else:
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
        # TODO: record the MAXRECURSION
        if test_eval:
            f_csv.writerow(['Solve timeout: %s' % solve_timeout, 'Eval timeout: %s' % eval_timeout])
        else:
            f_csv.writerow(['Solve timeout: %s' % solve_timeout, 'ProofTerm timeout: %s' % eval_timeout])
        f_csv.writerow(["Total time: %.3f" % (end_time - start_time)])
        f_csv.writerow([datetime.now().strftime('%Y-%m-%d %H:%M:%S')])