import unittest
import time
from smt.veriT.proof_parser import parse_decl, proof_parser
from smt.veriT import interface, proof_rec
import os

smtlib_path = None

try:
    with open('smt\\veriT\\tests\\smtlib_path.txt', 'r') as f:
        smtlib_path = f.readline().strip()
except FileNotFoundError:
    print("File smtlib_path.txt should be present in the smt/veriT/tests/ directory,")
    print("containing the path to the smtlib folder.")


def test_parse_step(verit_proof, ctx):
    parser = proof_parser(ctx)
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        k = parser.parse(s)

def test_file(filename, write_file=False, show_time=True):
    """Test a single SMT file.
    
    filename : str - absolute path of the file.
    write_file : bool - whether to write proof to proof.txt.
    show_time : bool - whether to display time taken.
    
    """
    global smtlib_path
    if not smtlib_path:
        return

    if filename[-4:] != 'smt2':
        return

    abs_name = smtlib_path + filename
    if interface.is_sat(abs_name):
        return
    print(repr(filename) + ',')

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(abs_name)
    ctx = proof_rec.bind_var(abs_name)
    solve_time = time.perf_counter() - start_time

    # Optional: write to file
    if write_file:
        with open('proof.txt', 'w') as f:
            f.write(verit_proof)

    # Parse
    start_time = time.perf_counter()
    test_parse_step(verit_proof, ctx)
    parse_time = time.perf_counter() - start_time

    if show_time:
        print("Solve: %.3f. Parse: %.3f" % (solve_time, parse_time))

def test_path(path):
    """Test a directory containing SMT files."""
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path
    if os.path.isdir(abs_path):
        # Input is a directory
        sub_paths = [path + '\\' + child for child in os.listdir(abs_path)]
        for sub_path in sub_paths:
            test_path(sub_path)
    else:
        # Input is a file
        test_file(path)


class ParserTest(unittest.TestCase): 
    def testParseQF_UF(self):
        test_paths = [
            'QF_UF\\20170829-Rodin\\smt1300175744189082250.smt2',
            'QF_UF\\20170829-Rodin\\smt1468783596909311386.smt2',
            'QF_UF\\20170829-Rodin\\smt2061505268723161891.smt2',
            'QF_UF\\20170829-Rodin\\smt2080745738819601301.smt2',
            'QF_UF\\20170829-Rodin\\smt2325451563592377472.smt2',
            'QF_UF\\20170829-Rodin\\smt249825283571301584.smt2',
            'QF_UF\\20170829-Rodin\\smt2598599073465845145.smt2',
            'QF_UF\\20170829-Rodin\\smt2970577543992530805.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_blocks.2.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_bridge.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_brp.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_bug-1_ab_cti_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_cache_coherence_three_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_cambridge.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_collision.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_counter_v_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_cyclic_scheduler.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_elevator.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_eq_sdp_v7_ab_cti_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_exit.1.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_extinction.2.prop1_ab_reg_max.smt2',
            'QF_UF\\2018-Goel-hwbench\\QF_UF_firewire_tree.1.prop1_ab_reg_max.smt2',
            'QF_UF\\20190906-CLEARSY',
            'QF_UF\\eq_diamond\\eq_diamond1.smt2',
            'QF_UF\\eq_diamond\\eq_diamond10.smt2',
            "QF_UF\\NEQ\\NEQ004_size4.smt2",
            "QF_UF\\NEQ\\NEQ004_size5.smt2",
            "QF_UF\\NEQ\\NEQ006_size3.smt2",
            "QF_UF\\PEQ\\PEQ012_size3.smt2",
            "QF_UF\\QG-classification\\loops6\\iso_icl103.smt2",
            "QF_UF\\QG-classification\\qg5\\iso_icl054.smt2",
            'QF_UF\\SEQ\\SEQ004_size5.smt2',
            'QF_UF\\SEQ\\SEQ004_size6.smt2',
            'QF_UF\\SEQ\\SEQ005_size7.smt2',
            "QF_UF\\TypeSafe\\z3.1184131.smt2",
            "QF_UF\\TypeSafe\\z3.1184147.smt2",
            "QF_UF\\TypeSafe\\z3.1184163.smt2",
        ]

        for path in test_paths:
            test_path(path)

    def testParseQF_UFLRA(self):
        test_paths = [
            # 'QF_UFLRA',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--i2c--algos--i2c-algo-pca.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--media--video--gspca--gspca_stv0680.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
        ]

        for path in test_paths:
            test_path(path)


if __name__ == "__main__":
    unittest.main()
