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

def test_file(filename, write_file=False, show_time=True, veriT_only=False):
    """Test a single SMT file.
    
    filename : str - absolute path of the file.
    write_file : bool - whether to write proof to proof.txt.
    show_time : bool - whether to display time taken.
    veriT_only : bool - only check whether veriT returns unsat.
    
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

    # Only check whether veriT returns unsat
    if veriT_only:
        return

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

def test_path(path, write_file=False, show_time=False, veriT_only=False):
    """Test a directory containing SMT files."""
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path
    if os.path.isdir(abs_path):
        # Input is a directory
        sub_paths = [path + '\\' + child for child in os.listdir(abs_path)]
        for sub_path in sub_paths:
            test_path(sub_path, write_file=write_file, show_time=show_time, veriT_only=veriT_only)
    else:
        # Input is a file
        test_file(path, write_file=write_file, show_time=show_time, veriT_only=veriT_only)


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
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--i2c--algos--i2c-algo-pca.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--media--video--gspca--gspca_stv0680.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--atm--adummy.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.diskperf_true-unreach-call.i.cil.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.email_spec27_product13_true-unreach-call.cil.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.gcd_1_true-unreach-call.i.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.minepump_spec1_product45_true-unreach-call.cil.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.Problem01_00_true-unreach-call.c.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.string_true-unreach-call.i.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.sum03_true-unreach-call_false-termination.i.smt2',
            'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.test_locks_10_true-unreach-call.c.smt2',
            'QF_UFLRA\\mathsat\\RandomCoupled\\pb_real_10_0200_10_14.smt2',
            'QF_UFLRA\\mathsat\\RandomCoupled\\pb_real_20_0400_10_12.smt2',
            'QF_UFLRA\\mathsat\\RandomCoupled\\pb_real_30_0600_10_13.smt2',
            'QF_UFLRA\\mathsat\\RandomCoupled\\pb_real_40_1000_10_18.smt2',
            'QF_UFLRA\\mathsat\\RandomDecoupled\\pb_real_30_60_45_06.smt2',
            'QF_UFLRA\\mathsat\\RandomDecoupled\\pb_real_40_80_60_01.smt2',
            'QF_UFLRA\\mathsat\\RandomDecoupled\\pb_real_50_100_30_07.smt2',
            'QF_UFLRA\\FFT\\smtlib.624882.smt2',
            'QF_UFLRA\\FFT\\smtlib.624898.smt2',
            'QF_UFLRA\\FFT\\smtlib.624916.smt2',
            'QF_UFLRA\\FFT\\smtlib.626139.smt2',
            'QF_UFLRA\\FFT\\smtlib.626159.smt2',
            'QF_UFLRA\\FFT\\smtlib.626179.smt2',
        ]

        for path in test_paths:
            test_path(path, veriT_only=True)


    def testParseQF_UFLIA(self):
        test_paths = [
            'QF_UFLIA\\mathsat\\EufLaArithmetic\\medium\\medium5.smt2',
            'QF_UFLIA\\mathsat\\EufLaArithmetic\\medium\\medium6.smt2',
            'QF_UFLIA\\mathsat\\EufLaArithmetic\\hard\\hard4.smt2',
            'QF_UFLIA\\mathsat\\EufLaArithmetic\\hard\\hard5.smt2',
            'QF_UFLIA\\mathsat\\Hash\\hash_uns_03_03.smt2',
            'QF_UFLIA\\mathsat\\Hash\\hash_uns_03_04.smt2',
            'QF_UFLIA\\mathsat\\Wisa\\xs-05-06-2-2-5-1.smt2',
            'QF_UFLIA\\mathsat\\Wisa\\xs-05-07-4-5-1-2.smt2',
            'QF_UFLIA\\TwoSquares\\smtlib.602033.smt2',
            'QF_UFLIA\\TwoSquares\\smtlib.602046.smt2',
            'QF_UFLIA\\TwoSquares\\smtlib.686126.smt2',
            'QF_UFLIA\\TwoSquares\\smtlib.769286.smt2',
            'QF_UFLIA\\wisas\\xs_5_10.smt2',
            'QF_UFLIA\\wisas\\xs_5_15.smt2',
            'QF_UFLIA\\wisas\\xs_5_5.smt2',
            'QF_UFLIA\\wisas\\xs_7_12.smt2',
        ]

        for path in test_paths:
            test_path(path, veriT_only=True)


if __name__ == "__main__":
    unittest.main()
