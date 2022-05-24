"""Run all smt files stored in examples"""
import time
import sys
import csv
from datetime import datetime

from kernel.report import ProofReport
from smt.veriT import proof_parser, proof_rec, command, interface
sys.setrecursionlimit(10000)

def test_parse_step(verit_proof, ctx):
    parser = proof_parser.proof_parser(ctx)
    steps = []
    for s in verit_proof.replace("\r", "").split("\n"):
        # print(s)
        if s == "unsat" or s == "":
            continue
        step = parser.parse(s)
        if isinstance(step, command.Step) and step.rule_name == "lia_generic":
            return [step]
        steps.append(step)

    return steps

def test_file(filename, test_eval=False, test_proofterm=False,
            step_limit=None, omit_proofterm=None, parse_assertion=False, test_expand=False):
    """Test a given file under eval or proofterm mode."""
    print(repr(filename) + ',')

    if parse_assertion:
        assts = proof_rec.get_assertions(filename)
    else:
        assts = set()

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(filename, timeout=100)
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
    ctx = proof_rec.bind_var(filename)
    steps = test_parse_step(verit_proof, ctx)
    parse_time = time.perf_counter() - start_time
    parse_time_str = "%.3f" % (time.perf_counter() - start_time)

    # lia_generic is not supported
    if len(steps) == 1 and steps[0].rule_name == "lia_generic":
        return [filename, solve_time_str, 'lia_generic', '', '']


    # Validation by macro.eval
    eval_time_str = ""
    if test_eval:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)
        pt = recon.validate(is_eval=True, step_limit=step_limit, omit_proofterm=omit_proofterm)
        eval_time = time.perf_counter() - start_time
        eval_time_str = "%.3f." % eval_time
        assert pt.rule != "sorry"
        print([filename, solve_time_str, parse_time_str, eval_time_str, len(steps)])
        return [filename, solve_time_str, parse_time_str, eval_time_str, len(steps)]

    # Validation by macro.get_proof_term
    proofterm_time_str = ""
    if test_proofterm:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)
        rpt = None
        if test_expand:
            rpt = ProofReport()
        pt = recon.validate(is_eval=False, step_limit=step_limit, omit_proofterm=omit_proofterm,
                            test_expand=test_expand, rpt=rpt)
        if test_expand:
            print(rpt)
        proofterm_time = time.perf_counter() - start_time
        proofterm_time_str = "%.3f." % proofterm_time
        assert pt.rule != "sorry"
        print([filename, solve_time_str, parse_time_str, proofterm_time_str, len(steps)])
        return [filename, solve_time_str, parse_time_str, proofterm_time_str, len(steps)]

def get_file_names():
    with open("./smt/veriT/example/test_files.txt") as f:
        return [l.strip() for l in f.readlines()]

if __name__ == "__main__":
    fs = get_file_names()
    test_eval = True
    test_expand = False
    assert len(sys.argv) == 2 and\
            sys.argv[1] in ("--eval", "--proofterm", "--expand"), "the argument\
                     should be --eval, --proofterm or --expand"
    if sys.argv[1] != "--eval":
        test_eval = False
    if sys.argv[1] == "--expand":
        test_expand = True
    
    if len(sys.argv) == 3: # test single file
        file_path = sys.argv[2]
        fs = [file_path]

    if test_expand:
        headers = ['filename', 'Solve', 'Parse', 'Expand ProofTerm', 'Steps']
    elif test_eval:
        headers = ['filename', 'Solve', 'Parse', 'Eval', 'Steps']
    else:        
        headers = ['filename', 'Solve', 'Parse', 'ProofTerm', 'Steps']
    start_time = time.perf_counter()
    results =  [test_file("./smt/veriT/example/"+smt_file, test_eval=test_eval,
                 test_proofterm=not test_eval, test_expand=test_expand) for smt_file in fs]
    end_time = time.perf_counter()
    with open("./smt/veriT/example/result.csv", "w", newline='') as f:
        f_csv = csv.writer(f)
        f_csv.writerow(headers)
        f_csv.writerows(results)
        f_csv.writerow(["Total time: %.3f" % (end_time - start_time)])
        f_csv.writerow([datetime.now().strftime('%Y-%m-%d %H:%M:%S')])