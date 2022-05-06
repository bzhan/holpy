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

from smt.veriT import interface, proof_rec, proof_parser
from syntax.settings import settings
settings.unicode = False

sys.setrecursionlimit(10000)


def test_parse_step(verit_proof, ctx):
    parser = proof_parser.proof_parser(ctx)
    steps = []
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        steps.append(parser.parse(s))

    return steps

def test_file(filename, verit_proof, test_eval=False):
    """Test a given file under eval or proofterm mode."""
    # Solve 
    start_time = time.perf_counter()
    ctx = proof_rec.bind_var(filename)
    solve_time = time.perf_counter() - start_time
    solve_time_str = "%.3f" % solve_time
    # Parse
    try: # parsing error
        steps = test_parse_step(verit_proof, ctx)
    except Exception as e:
        print("%s, %s, %s, %s, %s" % (filename, solve_time_str, 'PARSING ERROR (HolPy) %s' % e, '', ''))
        # print([filename, solve_time_str, 'PARSING ERROR (HolPy) %s' % e, '', ''])
    
    parse_time = time.perf_counter() - start_time
    parse_time_str = "%.3f" % parse_time    
    assts = proof_rec.get_assertions(filename)
    # Validation by macro.eval
    eval_time_str = ""
    if test_eval:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)
        try:
            pt = recon.validate(is_eval=True, with_bar=False)
        except Exception as e:
            print("%s, %s, %s, %s, %s" % (filename, solve_time_str, parse_time_str, 'Filename: %s Error: %s' % (str(filename), str(e)), len(steps)))
            # print([filename, solve_time_str, parse_time_str, 'Filename: %s Error: %s' % (str(filename), str(e)), len(steps)])                   
        eval_time = time.perf_counter() - start_time
        eval_time_str = "Eval: %.3f" % eval_time
        assert pt.rule != "sorry"

    if test_eval:
        print([filename, solve_time_str, parse_time_str, eval_time_str, len(steps)])

    # Validation by macro.get_proof_term
    proofterm_time_str = ""
    if not test_eval:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)

        try:
            pt = recon.validate(is_eval=False, with_bar=False)
        except Exception as e:
            # print([filename, solve_time_str, parse_time_str, 'Error: %s %s' % (str(filename), str(e)), len(steps)])
            print("%s, %s, %s, %s, %s" % (filename, solve_time_str, parse_time_str, 'Error: %s %s' % (str(filename), str(e)), len(steps)))
        proofterm_time = time.perf_counter() - start_time
        proofterm_time_str = "Proofterm: %.3f" % proofterm_time
        assert pt.rule != "sorry"

    if not test_eval:
        print("%s, %s, %s, %s, %s" % (filename, solve_time_str, parse_time_str, proofterm_time_str, len(steps)))
        # print([filename, solve_time_str, parse_time_str, proofterm_time_str, len(steps)])


# Parameters
# 1. filename
# 2. eval (--eval) or get_proof_term (--proofterm)
# 3. verit proof
if __name__ == "__main__":
    filename = sys.argv[1]
    test_eval = sys.argv[3]
    if test_eval == "false":
        test_eval = False
    else:
        test_eval = True
    verit_proof_file = sys.argv[2]
    with open (verit_proof_file) as f:
        verit_proof = f.read()
    test_file(filename, verit_proof, test_eval)