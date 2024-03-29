import unittest
import time
import os
from pstats import Stats
import cProfile
import sys

from kernel.report import ProofReport
from smt.veriT import interface, proof_rec, proof_parser, command
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

def test_file(filename, show_time=True, test_eval=False, test_proofterm=False,
              write_file=False, step_limit=None, omit_proofterm=None, parse_assertion=False,
              test_expand=False):
    """Test a given file under eval or proofterm mode."""
    global smtlib_path
    if not smtlib_path:
        return

    if filename[-4:] != 'smt2':
        return

    abs_name = smtlib_path + filename
    if not interface.is_unsat(abs_name, timeout=100):
        return
    print(repr(filename) + ',')

    if parse_assertion:
        assts = proof_rec.get_assertions(abs_name)
    else:
        assts = set()

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(abs_name, timeout=100)
    if verit_proof is None:
        return
    if verit_proof == "unknown\r\n":
        print("unknown proof")
        return
    ctx = proof_rec.bind_var(abs_name)
    solve_time = time.perf_counter() - start_time

    # Optional: write to file
    if write_file:
        with open('proof.txt', 'w') as f:
            f.write(verit_proof)

    # Parse
    start_time = time.perf_counter()
    steps = test_parse_step(verit_proof, ctx)
    parse_time = time.perf_counter() - start_time
    if len(steps) == 1 and isinstance(steps[0], command.Step) and steps[0].rule_name == "lia_generic":
        return

    # Validation by macro.eval
    eval_time_str = ""
    if test_eval:
        start_time = time.perf_counter()
        recon = proof_rec.ProofReconstruction(steps, smt_assertions=assts)
        pt = recon.validate(is_eval=True, step_limit=step_limit, omit_proofterm=omit_proofterm)
        eval_time = time.perf_counter() - start_time
        eval_time_str = "Eval: %.3f." % eval_time
        assert pt.rule != "sorry"

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
        proofterm_time_str = "Proofterm: %.3f." % proofterm_time
        assert pt.rule != "sorry"

    # Optional: print time
    if show_time:
        print("Solve: %.3f. Parse: %.3f. %s %s"
                    % (solve_time, parse_time, eval_time_str, proofterm_time_str))


def test_path(path, show_time=True, test_eval=False, test_proofterm=False,
              write_file=False, step_limit=None, omit_proofterm=None, parse_assertion=False,
              test_expand=False):
    """Test a directory containing SMT files.
    
    test_eval : bool - test evaluation of steps.
    test_proofterm : bool - test proof term reconstruction of steps.
    write_file : bool - whether to write proof to proof.txt.
    step_limit : [None, int] - limit on number of steps to test for each file.
    omit_proofterm : List[str] - list of macro names for which proof term reconstruction
        is omitted (evaluation is used instead).
        
    """
    global smtlib_path
    if not smtlib_path:
        return

    abs_path = smtlib_path + path

    if not os.path.exists(abs_path):
        print("Directory %s not found." % path)
        return

    if os.path.isdir(abs_path):
        # Input is a directory
        sub_paths = [path + '/' + child for child in os.listdir(abs_path)]
        for sub_path in sub_paths:
            test_path(sub_path, show_time=show_time, test_eval=test_eval, test_proofterm=test_proofterm,
                      write_file=write_file, step_limit=step_limit, omit_proofterm=omit_proofterm, parse_assertion=parse_assertion,
                      test_expand=test_expand)
    else:
        # Input is a file
        test_file(path, show_time=show_time, test_eval=test_eval, test_proofterm=test_proofterm,
                  write_file=write_file, step_limit=step_limit, omit_proofterm=omit_proofterm, parse_assertion=parse_assertion,
                  test_expand=test_expand)


class ProofrecTest(unittest.TestCase):
    def test_QF_UF(self): # proofterm ✓ eval ✓ expand ✓
        test_paths = [
            'QF_UF/20170829-Rodin/smt1300175744189082250.smt2',
            'QF_UF/20170829-Rodin/smt1468783596909311386.smt2',
            'QF_UF/20170829-Rodin/smt2061505268723161891.smt2',
            'QF_UF/20170829-Rodin/smt2080745738819601301.smt2',
            'QF_UF/20170829-Rodin/smt2325451563592377472.smt2',
            'QF_UF/20170829-Rodin/smt249825283571301584.smt2',
            'QF_UF/20170829-Rodin/smt2598599073465845145.smt2',
            'QF_UF/20170829-Rodin/smt2970577543992530805.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_blocks.2.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_bridge.1.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_brp.1.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_bug-1_ab_cti_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_h_TicTacToe_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_cache_coherence_three_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_cambridge.1.prop1_ab_reg_max.smt2',
            # 'QF_UF/2018-Goel-hwbench/QF_UF_sokoban.3.prop1_ab_br_max.smt2',  # distinct_elim
            'QF_UF/2018-Goel-hwbench/QF_UF_h_Vlunc_ab_cti_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_collision.1.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_counter_v_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_cyclic_scheduler.1.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_elevator.1.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_eq_sdp_v7_ab_cti_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_exit.1.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_extinction.2.prop1_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.1.prop1_ab_reg_max.smt2',
            'QF_UF/eq_diamond/eq_diamond1.smt2',
            'QF_UF/eq_diamond/eq_diamond10.smt2',
            "QF_UF/NEQ/NEQ004_size4.smt2",
            "QF_UF/NEQ/NEQ004_size5.smt2",
            "QF_UF/NEQ/NEQ006_size3.smt2",
            "QF_UF/PEQ/PEQ012_size3.smt2",
            "QF_UF/QG-classification/loops6/iso_icl103.smt2",
            "QF_UF/QG-classification/qg5/iso_icl054.smt2",
            'QF_UF/SEQ/SEQ004_size5.smt2',
            'QF_UF/SEQ/SEQ004_size6.smt2',
            'QF_UF/SEQ/SEQ005_size7.smt2',
            'QF_UF/SEQ/SEQ020_size2.smt2',
            "QF_UF/TypeSafe/z3.1184131.smt2",
            "QF_UF/TypeSafe/z3.1184147.smt2",
            "QF_UF/TypeSafe/z3.1184163.smt2",
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_QF_UFLRA(self): # proofterm ✓ eval ✓ expand ✓
        test_paths = [
            'QF_UFLRA/mathsat/RandomCoupled/pb_real_10_0200_10_14.smt2',
            'QF_UFLRA/mathsat/RandomCoupled/pb_real_20_0400_10_12.smt2',
            "QF_UFLRA/mathsat/RandomCoupled/pb_real_20_0500_10_25.smt2",
            'QF_UFLRA/mathsat/RandomCoupled/pb_real_30_0600_10_13.smt2',
            'QF_UFLRA/mathsat/RandomDecoupled/pb_real_30_60_45_06.smt2',
            'QF_UFLRA/mathsat/RandomDecoupled/pb_real_40_80_60_01.smt2',
            'QF_UFLRA/mathsat/RandomDecoupled/pb_real_50_100_30_07.smt2',
            'QF_UFLRA/FFT/smtlib.624882.smt2',
            'QF_UFLRA/FFT/smtlib.624898.smt2',
            'QF_UFLRA/FFT/smtlib.624916.smt2',
            'QF_UFLRA/FFT/smtlib.626139.smt2',
            'QF_UFLRA/FFT/smtlib.626159.smt2',
            'QF_UFLRA/FFT/smtlib.626179.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_QF_UFLIA(self): # proofterm ✓ eval ✓ expand ✓
        test_paths = [
            'QF_UFLIA/mathsat/EufLaArithmetic/medium/medium5.smt2',
            'QF_UFLIA/mathsat/EufLaArithmetic/medium/medium6.smt2',
            'QF_UFLIA/mathsat/EufLaArithmetic/hard/hard4.smt2',
            'QF_UFLIA/mathsat/EufLaArithmetic/hard/hard5.smt2',
            'QF_UFLIA/mathsat/Hash/hash_uns_03_03.smt2',
            'QF_UFLIA/mathsat/Hash/hash_uns_03_04.smt2',
            'QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2',
            'QF_UFLIA/mathsat/Wisa/xs-05-12-1-4-2-1.smt2',
            'QF_UFLIA/mathsat/Wisa/xs-05-16-1-5-4-3.smt2',
            'QF_UFLIA/TwoSquares/smtlib.602033.smt2',
            'QF_UFLIA/TwoSquares/smtlib.602046.smt2',
            'QF_UFLIA/TwoSquares/smtlib.686126.smt2',
            'QF_UFLIA/TwoSquares/smtlib.769286.smt2',
            'QF_UFLIA/TwoSquares/smtlib.686091.smt2',
            'QF_UFLIA/wisas/xs_7_12.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)


    def test_QF_UFIDL(self):
        test_paths = [
            'QF_UFIDL/pete2/c6_s.smt2',
            # 'QF_UFIDL/pete2/c9_s.smt2', #ite_simplify
            'QF_UFIDL/pete2/c7_s.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)


    def test_UF(self): # eval ✓ proofterm ✓ expand ✓
        test_paths = [
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_16_59_39_090_1045351.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_17_00_12_337_1079814.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_17_00_49_980_1120402.smt_in.smt2',
            "UF/20170428-Barrett/cdt-cade2015/nada/afp/lmirror/x2015_09_10_16_47_35_530_1067960.smt_in.smt2",
            "UF/20170428-Barrett/cdt-cade2015/nada/afp/lmirror/x2015_09_10_16_47_27_202_1060941.smt_in.smt2",
            "UF/20170428-Barrett/cdt-cade2015/nada/afp/huffman/x2015_09_10_16_49_30_501_1188113.smt_in.smt2",
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/huffman/x2015_09_10_16_48_25_033_1111490.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag/x2015_09_10_16_52_18_634_983654.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag/x2015_09_10_16_53_05_211_1033050.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag/x2015_09_10_16_53_31_362_1064389.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_48_45_757_1043506.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_54_30_307_1349771.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_57_04_292_1481164.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_56_13_740_1441286.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_17_07_59_177_2281818.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_56_12_258_1440056.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/huffman/x2015_09_10_16_51_19_087_1305640.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/sorted_list_operations/x2015_09_10_16_48_18_474_1105048.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_52_48_322_1388593.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_46_30_200_1001391.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_47_39_480_1078027.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_48_44_767_1147663.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_52_04_277_1342945.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/stream/x2015_09_10_16_47_52_499_1057641.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree/x2015_09_10_16_54_35_132_1014381.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree/x2015_09_10_16_54_53_474_1036287.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree/x2015_09_10_16_55_00_922_1043783.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/stern_brocot_tree/x2015_09_10_16_50_54_775_1033877.smt_in.smt2',
            'UF/sledgehammer/Arrow_Order/smtlib.578262.smt2',
            'UF/sledgehammer/Arrow_Order/smtlib.617784.smt2',
            'UF/sledgehammer/Arrow_Order/smtlib.686801.smt2',
            'UF/sledgehammer/Arrow_Order/uf.836907.smt2',
            'UF/sledgehammer/FFT/uf.549548.smt2',
            'UF/sledgehammer/FFT/uf.600765.smt2',
            'UF/sledgehammer/FFT/uf.626085.smt2',
            'UF/sledgehammer/FFT/uf.552859.smt2',
            'UF/sledgehammer/FFT/uf.605329.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.560771.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.590503.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.734512.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.1025050.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.1061982.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.1384400.smt2',
            'UF/sledgehammer/Hoare/smtlib.1170876.smt2',
            'UF/sledgehammer/Hoare/uf.655433.smt2',
            'UF/sledgehammer/Hoare/uf.1008477.smt2',
            'UF/sledgehammer/Hoare/uf.1031408.smt2',
            'UF/sledgehammer/Hoare/uf.1150909.smt2',
            'UF/sledgehammer/NS_Shared/smtlib.678332.smt2',
            'UF/sledgehammer/NS_Shared/uf.712214.smt2',
            'UF/sledgehammer/QEpres/uf.1039338.smt2',
            'UF/sledgehammer/QEpres/uf.716503.smt2',
            'UF/sledgehammer/QEpres/uf.717211.smt2',
            'UF/sledgehammer/StrongNorm/uf.701666.smt2',
            'UF/sledgehammer/TypeSafe/uf.913303.smt2',
            'UF/sledgehammer/TypeSafe/smtlib.1267524.smt2',
            'UF/sledgehammer/TwoSquares/uf.611567.smt2',
            'UF/sledgehammer/TwoSquares/uf.603183.smt2',
            'UF/sledgehammer/TwoSquares/uf.618437.smt2',
            'UF/sledgehammer/TwoSquares/uf.739998.smt2',
            'UF/sledgehammer/TwoSquares/uf.680734.smt2',
            'UF/sledgehammer/TwoSquares/uf.725943.smt2',
            'UF/sledgehammer/TwoSquares/uf.757144.smt2',
            'UF/grasshopper/instantiated/concat_check_heap_access_23_4.smt2',
            'UF/grasshopper/instantiated/concat_invariant_18_4.smt2',
            'UF/grasshopper/instantiated/dl_filter_postcondition_of_dl_filter_41_1.smt2',
            'UF/grasshopper/uninstantiated/dl_filter_loop_invariant_40_3.smt2',
            'UF/grasshopper/uninstantiated/dl_filter_postcondition_of_dl_filter_41_1.smt2',
            'UF/grasshopper/uninstantiated/dl_insert_check_heap_access_16_4.smt2', 
            'UF/misc/list1.smt2',
            'UF/misc/set10.smt2',
            'UF/misc/set11.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_UFLRA(self): # eval ✓ proofterm ✓ expand ✓
        test_paths = [
            'UFLRA/FFT/smtlib.620487.smt2',
            'UFLRA/FFT/smtlib.620535.smt2',
            'UFLRA/FFT/smtlib.623417.smt2',
            'UFLRA/FFT/smtlib.623474.smt2',
            'UFLRA/FFT/smtlib.623531.smt2',
            'UFLRA/FFT/smtlib.623597.smt2',
            'UFLRA/FFT/smtlib.627457.smt2',
            'UFLRA/FFT/smtlib.627531.smt2',
            'UFLRA/FFT/smtlib.627605.smt2',
            'UFLRA/FFT/smtlib.627688.smt2',
        ]

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

    def test_UFLIA(self): # eval ✓ proofterm ✓ expand ✓
        test_paths = [
            'UFLIA/boogie/AdditiveMethods_AdditiveMethods..ctor.smt2',
            'UFLIA/boogie/AdditiveMethods_AdditiveMethods.M.smt2',
            'UFLIA/boogie/AdditiveMethods_AdditiveMethods.N.smt2',
            'UFLIA/boogie/Array_test3.MyClass.M0_test3.MyClass.array_notnull.smt2',
            'UFLIA/boogie/Array_test3.MyClass.M1_test3.MyClass.array.array_notnull.smt2',
            'UFLIA/boogie/Array_test3.MyClass.M2_test3.MyClass.array2_notnull.smt2',
            'UFLIA/boogie/Change773_Test2.Foo.smt2',
            'UFLIA/check/bignum_quant.smt2',
            'UFLIA/misc/arr1.smt2',
            'UFLIA/misc/list3.smt2',
            'UFLIA/misc/list5.smt2',
            'UFLIA/RicartAgrawala/ricart-agrawala1.smt2',
            'UFLIA/sexpr/SES.Atom..ctor_System.String_notnull.smt2',
            'UFLIA/sexpr/SES.Atom.Write_System.IO.TextWriter_notnull.smt2',
            'UFLIA/simplify/javafe.ast.AmbiguousMethodInvocation.29.smt2',
            'UFLIA/simplify/javafe.ast.BinaryExpr.48.smt2',
            'UFLIA/simplify/javafe.ast.BlockStmt.50.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.AmbiguousMethodInvocation.001.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.AmbiguousVariableAccess.001.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.ArrayInit.001.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.CatchClauseVec.001.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.ThrowStmt.004.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.Identifier.005.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.tc.Types.002.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.util.StackVector.005.smt2',
            'UFLIA/simplify2/front_end_suite/javafe.ast.FormalParaDeclVec.015.smt2',
            'UFLIA/sledgehammer/Arrow_Order/smtlib.555057.smt2',
            'UFLIA/sledgehammer/Arrow_Order/smtlib.555849.smt2',
            'UFLIA/sledgehammer/Arrow_Order/smtlib.556254.smt2',
            'UFLIA/sledgehammer/FFT/smtlib.935892.smt2',
            'UFLIA/sledgehammer/TwoSquares/smtlib.871354.smt2',
            'UFLIA/sledgehammer/TwoSquares/smtlib.832972.smt2',
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1438328.smt2',
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1438517.smt2',
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1437253.smt2',
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1437948.smt2',
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1081041.smt2',
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1080151.smt2',
            'UFLIA/sledgehammer/Hoare/smtlib.750663.smt2',
            'UFLIA/sledgehammer/Hoare/smtlib.1046517.smt2',
            'UFLIA/sledgehammer/QEpres/smtlib.1113749.smt2',
            'UFLIA/spec_sharp/textbook-DutchFlag.bpl.1.Partition.smt2',
            'UFLIA/spec_sharp/textbook-Find.bpl.1.Find.smt2',
            'UFLIA/spec_sharp/textbook-Find.bpl.2.Main.smt2',
            'UFLIA/tokeneer/admin/finishop-1.smt2',
            'UFLIA/tokeneer/admin/init-1.smt2',
            'UFLIA/tokeneer/admin/logon-1.smt2',
            'UFLIA/tokeneer/admin/opisavailable-4.smt2',
            'UFLIA/tokeneer/admin/opisavailable-27.smt2',
            'UFLIA/tokeneer/certificatestore/updatestore-19.smt2',
            'UFLIA/tokeneer/certificatestore/updatestore-18.smt2',
            'UFLIA/tokeneer/configdata/validatefile/readaccesspolicy-6.smt2',
            'UFLIA/tokeneer/configdata/validatefile/readclass-5.smt2',
            'UFLIA/tptp/ARI604=1.smt2',
            'UFLIA/tptp/ARI612=1.smt2',
            'UFLIA/tptp/ARI615=1.smt2',
            'UFLIA/grasshopper/uninstantiated/union_postcondition_of_union_36_8.smt2',
            'UFLIA/grasshopper/instantiated/merge_loop_invariant_61_3.smt2',
            'UFLIA/grasshopper/instantiated/pull_strands_loop_invariant_101_3.smt2',
            'UFLIA/grasshopper/instantiated/split_postcondition_of_split_88_1.smt2',
            'UFLIA/grasshopper/instantiated/filter_loop_invariant_48_3.smt2'
        ]
        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)


    # def test_QF_IDL(self): # eval ✓ proofterm: ✓
    #     test_paths = [
    #         'QF_IDL/planning/plan-40.cvc.smt2',
    #         # 'QF_IDL/RTCL/b13_tf_15/ckt_PROP5_tf_15.smt2', # timeout
    #     ]
    #     profile = False
    #     if profile:
    #         pr = cProfile.Profile()
    #         pr.enable()

    #     for path in test_paths:
    #         test_path(path, test_proofterm=True, parse_assertion=True)

    #     if profile:
    #         p = Stats(pr)
    #         p.strip_dirs()
    #         p.sort_stats('cumtime')
    #         p.print_stats(50)

    # def test_QF_RDL(self): # eval ✓ proofterm: ac_simp
    #     test_paths = [
    #         # 'QF_RDL/skdmxa/skdmxa-3x3-5.smt2' # ac_simp
    #     ]

    #     profile = False
    #     if profile:
    #         pr = cProfile.Profile()
    #         pr.enable()

    #     for path in test_paths:
    #         test_path(path, test_proofterm=True, parse_assertion=True)

    #     if profile:
    #         p = Stats(pr)
    #         p.strip_dirs()
    #         p.sort_stats('cumtime')
    #         p.print_stats(50)

    def test_QF_LRA(self): # proofterm ✓ eval ✓ expand ✓
        test_paths = [
            'QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_count_by_k.i_3_3_2.bpl_7.smt2',
            'QF_LRA/sal/carpark/Carpark2-ausgabe-1.smt2',
            'QF_LRA/spider_benchmarks/current_frame.induction.smt2',
            'QF_LRA/sc/sc-10.base.cvc.smt2',
            'QF_LRA/uart/uart-10.base.cvc.smt2',
            'QF_LRA/clock_synchro/clocksynchro_9clocks.main_invar.base.smt2',
            'QF_LRA/clock_synchro/clocksynchro_8clocks.main_invar.base.smt2',
            'QF_LRA/clock_synchro/clocksynchro_5clocks.main_invar.base.smt2',
            'QF_LRA/clock_synchro/clocksynchro_4clocks.main_invar.base.smt2',
            'QF_LRA/clock_synchro/clocksynchro_7clocks.main_invar.base.smt2',
            'QF_LRA/clock_synchro/clocksynchro_6clocks.main_invar.base.smt2',
            'QF_LRA/clock_synchro/clocksynchro_3clocks.main_invar.base.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_QF_AUFLIA(self): # eval ✓ proofterm ✓ expand ✓
        test_paths = [
            'QF_AUFLIA/20170829-Rodin/smt101358492275879472.smt2',
            'QF_AUFLIA/20170829-Rodin/smt1048206973303286471.smt2',
            'QF_AUFLIA/20170829-Rodin/smt1076382332286802622.smt2',
            'QF_AUFLIA/20170829-Rodin/smt9116345646566616227.smt2',
            'QF_AUFLIA/20170829-Rodin/smt957085527369554317.smt2',
            'QF_AUFLIA/20170829-Rodin/smt971450140125177067.smt2',
            'QF_AUFLIA/20170829-Rodin/smt1656603882241727713.smt2',
            'QF_AUFLIA/cvc/add4.smt2',
            'QF_AUFLIA/cvc/add5.smt2',
            'QF_AUFLIA/cvc/add6.smt2',
            'QF_AUFLIA/cvc/fb_var_33_6.smt2',
            'QF_AUFLIA/cvc/pp-invariant.smt2',
            'QF_AUFLIA/cvc/pp-pc-s2i.smt2',
            'QF_AUFLIA/cvc/read6.smt2',
            'QF_AUFLIA/swap/swap_t1_pp_nf_ai_00002_001.cvc.smt2',
            'QF_AUFLIA/swap/swap_t1_pp_nf_ai_00003_003.cvc.smt2',
            'QF_AUFLIA/swap/swap_t1_pp_nf_ai_00008_003.cvc.smt2',
            'QF_AUFLIA/swap/swap_t1_pp_sf_ai_00002_001.cvc.smt2',
            'QF_AUFLIA/swap/swap_t1_pp_sf_ai_00003_003.cvc.smt2',
            'QF_AUFLIA/swap/swap_t1_pp_sf_ai_00008_003.cvc.smt2',
            'QF_AUFLIA/swap/swap_t3_pp_nf_ai_00005_001.cvc.smt2',
            'QF_AUFLIA/swap/swap_t3_pp_sf_ai_00005_001.cvc.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_AUFLIA(self): # eval ✓ proofterm ✓ expand ✓
        test_paths = [
            'AUFLIA/20170829-Rodin/smt1857914508354494859.smt2',
            # 'AUFLIA/20170829-Rodin/smt8562182281812961752.smt2', # resolution
            # 'AUFLIA/20170829-Rodin/smt872164429150466761.smt2',  # resolution
            # 'AUFLIA/20170829-Rodin/smt1012188733744711688.smt2',  # onepoint
            'AUFLIA/20170829-Rodin/smt1002232729905089644.smt2',
            'AUFLIA/20170829-Rodin/smt1005619206308662052.smt2',
            'AUFLIA/20170829-Rodin/smt1041855950602319657.smt2',
            'AUFLIA/20170829-Rodin/smt1056800823907916951.smt2',
            'AUFLIA/20170829-Rodin/smt1092100299585472351.smt2',
            'AUFLIA/20170829-Rodin/smt1119354235255245041.smt2',
            'AUFLIA/20170829-Rodin/smt121642227126350719.smt2',
            'AUFLIA/20170829-Rodin/smt1218456647866960210.smt2',
            'AUFLIA/20170829-Rodin/smt1238392701218460929.smt2',
            'AUFLIA/20170829-Rodin/smt1306673360382824160.smt2',
            'AUFLIA/20170829-Rodin/smt1404749150926468013.smt2',
            'AUFLIA/20170829-Rodin/smt6890534299883019152.smt2',
            'AUFLIA/20170829-Rodin/smt1548357652033660278.smt2',
            'AUFLIA/20170829-Rodin/smt1551255090000261050.smt2',
            'AUFLIA/20170829-Rodin/smt1553283421285438203.smt2',
            'AUFLIA/20170829-Rodin/smt1638875703304617187.smt2',
            'AUFLIA/20170829-Rodin/smt1643313206004053741.smt2',
            'AUFLIA/20170829-Rodin/smt1643358356540277150.smt2',
            'AUFLIA/20170829-Rodin/smt1828334434025716862.smt2',
            'AUFLIA/20170829-Rodin/smt1829029808963281215.smt2',
            'AUFLIA/20170829-Rodin/smt1882594910272367920.smt2',
            'AUFLIA/20170829-Rodin/smt1883437689668062427.smt2',
            'AUFLIA/20170829-Rodin/smt2022486099146293362.smt2',
            'AUFLIA/20170829-Rodin/smt2025463987927880021.smt2',
            'AUFLIA/20170829-Rodin/smt2027035001350841448.smt2',
            'AUFLIA/20170829-Rodin/smt2283324634047097920.smt2',
            'AUFLIA/20170829-Rodin/smt2885702086782097441.smt2',
            'AUFLIA/20170829-Rodin/smt8020508299917860570.smt2',
            'AUFLIA/20170829-Rodin/smt1053503323401967250.smt2',
            'AUFLIA/20170829-Rodin/smt2972435604341125203.smt2',
            'AUFLIA/20170829-Rodin/smt2020844136539587643.smt2',
            'AUFLIA/20170829-Rodin/smt7430161103589433024.smt2',
            'AUFLIA/20170829-Rodin/smt6884874971925634308.smt2',
            'AUFLIA/20170829-Rodin/smt962592699688307113.smt2',
            'AUFLIA/20170829-Rodin/smt5692365801843027532.smt2',
            'AUFLIA/20170829-Rodin/smt1077199842095303803.smt2',
            'AUFLIA/20170829-Rodin/smt8260763450980098018.smt2',
            'AUFLIA/20170829-Rodin/smt1220722083703635536.smt2',
            'AUFLIA/20170829-Rodin/smt7351897299178954133.smt2',
            'AUFLIA/20170829-Rodin/smt4213031790546145760.smt2',
            'AUFLIA/20170829-Rodin/smt4473657298807368490.smt2',
            'AUFLIA/20170829-Rodin/smt28921856381296720.smt2',
            'AUFLIA/20170829-Rodin/smt3504742795329872706.smt2',
            'AUFLIA/20170829-Rodin/smt7175126839151094124.smt2',
            # 'AUFLIA/20170829-Rodin/smt5586736073099019802.smt2', # resolution
            'AUFLIA/20170829-Rodin/smt1524510508476207618.smt2',
            'AUFLIA/20170829-Rodin/smt3939123684161216825.smt2',
            'AUFLIA/misc/set1.smt2',
            'AUFLIA/20170829-Rodin/smt8259835323357410578.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, test_expand=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_LRA(self): # eval ✓ proofterm ✓
        test_paths = [
            'LRA/scholl-smt08/RND/RND_3_15.smt2',
            'LRA/scholl-smt08/RND/RND_3_19.smt2',
            'LRA/scholl-smt08/RND/RND_3_28.smt2',
            'LRA/scholl-smt08/RND/RND_3_9.smt2',
            'LRA/scholl-smt08/RND/RND_4_12.smt2',
            'LRA/scholl-smt08/RND/RND_4_2.smt2',
            'LRA/scholl-smt08/RND/RND_4_7.smt2',
            'LRA/keymaera/intersection-example-simple.proof-node6512.smt2',
            'LRA/keymaera/intersection-example-simple.proof-node47049.smt2',
            'LRA/keymaera/intersection-example-simple.proof-node684031.smt2',
            'LRA/keymaera/intersection-example-simple.proof-node403143.smt2',
            'LRA/keymaera/intersection-example-simple.proof-node62694.smt2',
            'LRA/scholl-smt08/RND/RND_4_30.smt2',
        ]
        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_LIA(self): # eval ✓ proofterm ✓
        test_paths = [
            'LIA/UltimateAutomizer/MADWiFi-encode_ie_ok_true-unreach-call.i_17.smt2',
            'LIA/UltimateAutomizer/Primes_true-unreach-call.c_678.smt2',
            'LIA/UltimateAutomizer/recHanoi03_true-unreach-call_true-termination.c_2175.smt2',
            'LIA/UltimateAutomizer/recHanoi03_true-unreach-call_true-termination.c_557.smt2',
            'LIA/tptp/NUM865=1.smt2',
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_UF_DEBUG(self):
        test_paths = [                
            # 'UF/sledgehammer/TwoSquares/uf.602601.smt2',
            # 'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.903234.smt2',
            # 'UF/sledgehammer/Hoare/uf.828950.smt2',
        ]
        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_QF_LIA(self):
        test_paths = [
            'QF_LIA/rings/ring_2exp10_9vars_0ite_unsat.smt2',
            'QF_LIA/rings_preprocessed/ring_2exp4_7vars_2ite_unsat.smt2',
            'QF_LIA/cut_lemmas/15-vars/cut_lemma_02_004.smt2',
            'QF_LIA/check/int_incompleteness1.smt2',
            'QF_LIA/cut_lemmas/15-vars/cut_lemma_03_013.smt2',
            'QF_LIA/rings/ring_2exp16_8vars_0ite_unsat.smt2',
            'QF_LIA/rings/ring_2exp8_7vars_0ite_unsat.smt2',
            'QF_LIA/rings/ring_2exp8_6vars_0ite_unsat.smt2',
            'QF_LIA/rings/ring_2exp10_6vars_0ite_unsat.smt2',
            'QF_LIA/cut_lemmas/10-vars/cut_lemma_01_001.smt2',
            'QF_LIA/check/int_incompleteness1.smt2',
            'QF_LIA/CAV_2009_benchmarks/smt/10-vars/problem_2__026.smt2',
            'QF_LIA/Averest/parallel_prefix_sum/ParallelPrefixSum_safe_bgmc002.smt2', # timeout
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)

    def test_bug(self):
        test_paths = [
            'UF\\20170428-Barrett\\cdt-cade2015\\nada\\afp\\abstract_completeness\\x2015_09_10_16_59_39_090_1045351.smt_in.smt2', # bind
            'QF_UFLIA\\wisas\\xs_5_5.smt2', # resolution one proof term for twice
            'UFLIA\\misc\\list5.smt2', # resolution extra double negation in the result.
            'UFLIA/sledgehammer/TwoSquares/smtlib.832972.smt2', # ite_intro
            'UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1438328.smt2', # th_resolution
            'UF/sledgehammer/Arrow_Order/smtlib.617784.smt2', # bind suspected name conflict
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.560771.smt2', # th_resolution
        ]

        profile = False
        if profile:
            pr = cProfile.Profile()
            pr.enable()

        for path in test_paths:
            test_path(path, test_proofterm=True, parse_assertion=True, write_file=False)

        if profile:
            p = Stats(pr)
            p.strip_dirs()
            p.sort_stats('cumtime')
            p.print_stats(50)


if __name__ == "__main__":
    unittest.main()
