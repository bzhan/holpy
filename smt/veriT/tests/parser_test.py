import unittest
import time

from smt.veriT.proof_parser import parse_decl, proof_parser
from smt.veriT import interface, proof_rec
from smt.veriT import command
import os
from syntax.settings import settings
settings.unicode = False

smtlib_path = None

try:
    with open('smt/veriT/tests/smtlib_path.txt', 'r') as f:
        smtlib_path = f.readline().strip()
except FileNotFoundError:
    print("File smtlib_path.txt should be present in the smt/veriT/tests/ directory,")
    print("containing the path to the smtlib folder.")


def test_parse_step(verit_proof, ctx):
    parser = proof_parser(ctx)
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        step = parser.parse(s)
        if isinstance(step, command.Step) and step.rule_name == "lia_generic":
            print('lia_generic')

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
    if not interface.is_unsat(abs_name):
        print('sat / unknown / unsupported')
        return
    print(repr(filename) + ',')

    # Only check whether veriT returns unsat
    if veriT_only:
        # Check proof can be generated as well
        verit_proof = interface.solve(abs_name)
        return

    # Solve
    start_time = time.perf_counter()
    verit_proof = interface.solve(abs_name)
    if verit_proof is None:
        return

    if len(verit_proof) == 0:
        print('Empty proof')
        return

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

    if not os.path.exists(abs_path):
        print("Directory %s not found." % path)
        return

    if os.path.isdir(abs_path):
        # Input is a directory
        sub_paths = [path + '/' + child for child in os.listdir(abs_path)]
        for sub_path in sub_paths:
            test_path(sub_path, write_file=write_file, show_time=show_time, veriT_only=veriT_only)
    else:
        # Input is a file
        test_file(path, write_file=write_file, show_time=show_time, veriT_only=veriT_only)


class ParserTest(unittest.TestCase): 
    def testParseQF_UF(self):
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
            'QF_UF/2018-Goel-hwbench/QF_UF_cache_coherence_three_ab_reg_max.smt2',
            'QF_UF/2018-Goel-hwbench/QF_UF_cambridge.1.prop1_ab_reg_max.smt2',
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
            "QF_UF/TypeSafe/z3.1184131.smt2",
            "QF_UF/TypeSafe/z3.1184147.smt2",
            "QF_UF/TypeSafe/z3.1184163.smt2",
        ]

        for path in test_paths:
            test_path(path)

    def testParseQF_UFLRA(self):
        test_paths = [
            'QF_UFLRA/mathsat/RandomCoupled/pb_real_10_0200_10_14.smt2',
            'QF_UFLRA/mathsat/RandomCoupled/pb_real_20_0400_10_12.smt2',
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

        for path in test_paths:
            test_path(path)


    def testParseQF_UFLIA(self):
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
            'QF_UFLIA/wisas/xs_7_12.smt2',
        ]

        for path in test_paths:
            test_path(path)


    def testParseUF(self):
        test_paths = [
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_16_59_39_090_1045351.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_17_00_12_337_1079814.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness/x2015_09_10_17_00_49_980_1120402.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag/x2015_09_10_16_52_18_634_983654.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag/x2015_09_10_16_53_05_211_1033050.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag/x2015_09_10_16_53_31_362_1064389.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_48_45_757_1043506.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_54_30_307_1349771.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_16_57_04_292_1481164.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_46_30_200_1001391.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_47_39_480_1078027.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang/x2015_09_10_16_48_44_767_1147663.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree/x2015_09_10_16_54_35_132_1014381.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree/x2015_09_10_16_54_53_474_1036287.smt_in.smt2',
            'UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree/x2015_09_10_16_55_00_922_1043783.smt_in.smt2',
            'UF/sledgehammer/Arrow_Order/smtlib.578262.smt2',
            'UF/sledgehammer/Arrow_Order/smtlib.617784.smt2',
            'UF/sledgehammer/Arrow_Order/smtlib.686801.smt2',
            'UF/sledgehammer/FFT/uf.549548.smt2',
            'UF/sledgehammer/FFT/uf.600765.smt2',
            'UF/sledgehammer/FFT/uf.626085.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.1025050.smt2',
            'UF/sledgehammer/Fundamental_Theorem_Algebra/uf.1061982.smt2',
            'UF/sledgehammer/Hoare/smtlib.1170876.smt2',
            'UF/sledgehammer/Hoare/uf.1008477.smt2',
            'UF/sledgehammer/Hoare/uf.1031408.smt2',
            'UF/sledgehammer/StrongNorm/uf.701666.smt2',
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

        for path in test_paths:
            test_path(path)

    def testParseUFLRA(self):
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
            test_path(path)


    def testParseUFLIA(self):
        test_paths = [
            'UFLIA/boogie/AdditiveMethods_AdditiveMethods..ctor.smt2',
            'UFLIA/boogie/AdditiveMethods_AdditiveMethods.M.smt2',
            'UFLIA/boogie/AdditiveMethods_AdditiveMethods.N.smt2',
            'UFLIA/boogie/Array_test3.MyClass.M0_test3.MyClass.array_notnull.smt2',
            'UFLIA/boogie/Array_test3.MyClass.M1_test3.MyClass.array.array_notnull.smt2',
            'UFLIA/boogie/Array_test3.MyClass.M2_test3.MyClass.array2_notnull.smt2',
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
            'UFLIA/sledgehammer/Arrow_Order/smtlib.555057.smt2',
            'UFLIA/sledgehammer/Arrow_Order/smtlib.555849.smt2',
            'UFLIA/sledgehammer/Arrow_Order/smtlib.556254.smt2',
            'UFLIA/spec_sharp/textbook-DutchFlag.bpl.1.Partition.smt2',
            'UFLIA/spec_sharp/textbook-Find.bpl.1.Find.smt2',
            'UFLIA/spec_sharp/textbook-Find.bpl.2.Main.smt2',
            'UFLIA/tokeneer/admin/finishop-1.smt2',
            'UFLIA/tokeneer/admin/init-1.smt2',
            'UFLIA/tokeneer/admin/logon-1.smt2',
            'UFLIA/tptp/ARI604=1.smt2',
            'UFLIA/tptp/ARI612=1.smt2',
            'UFLIA/tptp/ARI615=1.smt2',
        ]

        for path in test_paths:
            test_path(path)


if __name__ == "__main__":
    unittest.main()
