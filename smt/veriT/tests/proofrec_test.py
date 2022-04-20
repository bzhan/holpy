import unittest
import time
import os
from pstats import Stats
import cProfile

from smt.veriT import interface, proof_rec, proof_parser
from syntax.settings import settings
settings.unicode = False

smtlib_path = None

try:
    with open('smt\\veriT\\tests\\smtlib_path.txt', 'r') as f:
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

def test_validate_step(verit_proof, is_eval=True):
    recon = proof_rec.ProofReconstruction(verit_proof)
    return recon.validate(is_eval)

def test_file(filename, show_time=True, test_eval=False, test_proofterm=False):
    """"""
    global smtlib_path
    if not smtlib_path:
        return

    if filename[-4:] != 'smt2':
        return

    abs_name = smtlib_path + filename
    if not interface.is_unsat(abs_name):
        return
    print(repr(filename) + ',')

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(abs_name)
    if verit_proof is None:
        return
    ctx = proof_rec.bind_var(abs_name)
    solve_time = time.perf_counter() - start_time

    # Parse
    start_time = time.perf_counter()
    steps = test_parse_step(verit_proof, ctx)
    parse_time = time.perf_counter() - start_time

    # Validation by macro.eval
    eval_time_str = ""
    if test_eval:
        start_time = time.perf_counter()
        pt1 = test_validate_step(steps)
        eval_time = time.perf_counter() - start_time
        eval_time_str = "Eval: %.3f." % eval_time
        # assert pt1.rule != "sorry"

    # Validation by macro.get_proof_term
    proofterm_time_str = ""
    if test_proofterm:
        start_time = time.perf_counter()
        pt2 = test_validate_step(steps, is_eval=False)
        proofterm_time = time.perf_counter() - start_time
        proofterm_time_str = "Proofterm: %.3f." % proofterm_time
        # assert pt2.rule != "sorry"

    # Optional: print time
    if show_time:
        print("Solve: %.3f. Parse: %.3f. %s %s"
                    % (solve_time, parse_time, eval_time_str, proofterm_time_str))


def test_path(path, show_time=True, test_eval=False, test_proofterm=False):
    """Test a directory containing SMT files."""
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path

    if not os.path.exists(abs_path):
        print("Directory %s not found." % path)
        return

    if os.path.isdir(abs_path):
        # Input is a directory
        sub_paths = [path + '\\' + child for child in os.listdir(abs_path)]
        for sub_path in sub_paths:
            test_path(sub_path, show_time=show_time, test_eval=test_eval, test_proofterm=test_proofterm)
    else:
        # Input is a file
        test_file(path, show_time=show_time, test_eval=test_eval, test_proofterm=test_proofterm)





class ProofrecTest(unittest.TestCase):
    def test_QF_UF(self):
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
            "QF_UF\\TypeSafe\\z3.1184131.smt2",
            "QF_UF\\TypeSafe\\z3.1184147.smt2",
            "QF_UF\\TypeSafe\\z3.1184163.smt2",
            'QF_UF\\eq_diamond\\eq_diamond1.smt2',
            'QF_UF\\eq_diamond\\eq_diamond2.smt2',
            # "QF_UF\\NEQ\\NEQ004_size4.smt2",
            # "QF_UF\\NEQ\\NEQ004_size5.smt2",
            # "QF_UF\\NEQ\\NEQ006_size3.smt2",
            # "QF_UF\\PEQ\\PEQ012_size3.smt2",
            "QF_UF\\QG-classification\\loops6\\iso_icl103.smt2",
            "QF_UF\\QG-classification\\qg5\\iso_icl054.smt2",
            # 'QF_UF\\SEQ\\SEQ004_size5.smt2',
            # 'QF_UF\\SEQ\\SEQ004_size6.smt2',
            # 'QF_UF\\SEQ\\SEQ005_size7.smt2',
            "QF_UF\\TypeSafe\\z3.1184131.smt2",
            "QF_UF\\TypeSafe\\z3.1184147.smt2",
            "QF_UF\\TypeSafe\\z3.1184163.smt2",
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_eval=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats()

    def test_UF(self):
        test_paths = [
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\abstract_completeness\\x2015_09_10_16_59_39_090_1045351.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\abstract_completeness\\x2015_09_10_17_00_12_337_1079814.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\abstract_completeness\\x2015_09_10_17_00_49_980_1120402.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\bindag\\x2015_09_10_16_52_18_634_983654.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\bindag\\x2015_09_10_16_53_05_211_1033050.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\bindag\\x2015_09_10_16_53_31_362_1064389.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\coinductive_list\\x2015_09_10_16_48_45_757_1043506.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\coinductive_list\\x2015_09_10_16_54_30_307_1349771.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\coinductive_list\\x2015_09_10_16_57_04_292_1481164.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\distro\\gram_lang\\x2015_09_10_16_46_30_200_1001391.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\distro\\gram_lang\\x2015_09_10_16_47_39_480_1078027.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\distro\\gram_lang\\x2015_09_10_16_48_44_767_1147663.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\gandl\\bird_tree\\x2015_09_10_16_54_35_132_1014381.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\gandl\\bird_tree\\x2015_09_10_16_54_53_474_1036287.smt_in.smt2',
            # 'UF\\20170428-Barrett\\cdt-cade2015\\nada\\gandl\\bird_tree\\x2015_09_10_16_55_00_922_1043783.smt_in.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_eval=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats()

    def test_QF_UFLRA(self):
        test_paths = [
            # 'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--i2c--algos--i2c-algo-pca.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            # 'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--media--video--gspca--gspca_stv0680.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            # 'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.43_1a_cilled_true-unreach-call_ok_nondet_linux-43_1a-drivers--atm--adummy.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c.smt2',
            # 'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.diskperf_true-unreach-call.i.cil.c.smt2',
            # 'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.email_spec27_product13_true-unreach-call.cil.c.smt2',
            # 'QF_UFLRA\\cpachecker-induction-svcomp14\\cpachecker-induction.gcd_1_true-unreach-call.i.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_eval=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats()

    def test_QF_UFLIA(self):
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

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_eval=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats()

