import unittest
import time
from smt.veriT.proof_parser import parse_decl, proof_parser
from smt.veriT import interface, proof_rec
import os


def get_smtlib_path():
    try:
        with open('smt\\veriT\\tests\\smtlib_path.txt', 'r') as f:
            return f.readline().strip()
    except FileNotFoundError:
        print("File smtlib_path.txt should be present in the smt/veriT/tests/ directory,")
        print("containing the path to the smtlib folder.")
        return None

def test_parse_step(verit_proof, ctx):
    parser = proof_parser(ctx)
    for s in verit_proof.replace("\r", "").split("\n"):
        if s == "unsat" or s == "":
            continue
        k = parser.parse(s)

class ParserTest(unittest.TestCase): 
    def testParseQF_UF(self):
        test_dirs = [
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
            # 'QF_UF\\20190906-CLEARSY\\0000\\',
            # 'QF_UF\\20190906-CLEARSY\\0001\\',
            # 'QF_UF\\20190906-CLEARSY\\0004\\',
            # 'QF_UF\\20190906-CLEARSY\\0005\\',
            # 'QF_UF\\20190906-CLEARSY\\0008\\',
            # 'QF_UF\\20190906-CLEARSY\\0009\\',
            # 'QF_UF\\20190906-CLEARSY\\0014\\',
            # 'QF_UF\\20190906-CLEARSY\\0015\\',
            # 'QF_UF\\20190906-CLEARSY\\0016\\',
            # 'QF_UF\\20190906-CLEARSY\\0021\\',
            # 'QF_UF\\20190906-CLEARSY\\0022\\',
            # 'QF_UF\\20190906-CLEARSY\\0023\\',
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

        smtlib_path = get_smtlib_path()
        if not smtlib_path:
            return

        show_time = True
        write_file = False

        for test_dir in test_dirs:
            abs_path = smtlib_path + test_dir
            if os.path.isdir(abs_path):
                # Input is a directory
                file_names = [test_dir + file for file in os.listdir(abs_path)]
            else:
                # Input is a file
                file_names = [test_dir]
            for file_name in file_names:
                abs_name = smtlib_path + file_name
                if interface.is_sat(abs_name):
                    continue
                print(repr(file_name) + ',')

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


if __name__ == "__main__":
    unittest.main()
