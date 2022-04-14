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
            # 'QF_UF\\20170829-Rodin\\smt1300175744189082250.smt2',
            # 'QF_UF\\20170829-Rodin\\smt1468783596909311386.smt2',
            # 'QF_UF\\20170829-Rodin\\smt2061505268723161891.smt2',
            # 'QF_UF\\20170829-Rodin\\smt2080745738819601301.smt2',
            # 'QF_UF\\20170829-Rodin\\smt2325451563592377472.smt2',
            # 'QF_UF\\20170829-Rodin\\smt249825283571301584.smt2',
            # 'QF_UF\\20170829-Rodin\\smt2598599073465845145.smt2',
            # 'QF_UF\\20170829-Rodin\\smt2970577543992530805.smt2',
            # 'QF_UF\\20170829-Rodin\\smt3166111930664231918.smt2',
            # 'QF_UF\\20170829-Rodin\\smt3534838651727683253.smt2',
            # 'QF_UF\\20170829-Rodin\\smt4057580428149921510.smt2',
            # 'QF_UF\\20170829-Rodin\\smt4458073420585573738.smt2',
            # 'QF_UF\\20170829-Rodin\\smt5144869669709662262.smt2',
            # 'QF_UF\\20170829-Rodin\\smt5490086717622526120.smt2',
            # 'QF_UF\\20170829-Rodin\\smt5801285361354912971.smt2',
            # 'QF_UF\\20170829-Rodin\\smt5832055835117075398.smt2',
            # 'QF_UF\\20170829-Rodin\\smt6739662804326223632.smt2',
            # 'QF_UF\\20170829-Rodin\\smt7452810379672948208.smt2',
            # 'QF_UF\\20170829-Rodin\\smt7632939434921259240.smt2',
            # 'QF_UF\\20170829-Rodin\\smt7665342989239969743.smt2',
            # 'QF_UF\\eq_diamond\\eq_diamond1.smt2',
            # 'QF_UF\\eq_diamond\\eq_diamond10.smt2',
            "QF_UF\\NEQ\\"
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
                c = proof_rec.bind_var(abs_name)
                solve_time = time.perf_counter() - start_time

                # Optional: write to file
                if write_file:
                    with open('proof.txt', 'w') as f:
                        f.write(verit_proof)

                # Parse
                start_time = time.perf_counter()
                test_parse_step(verit_proof, c)
                parse_time = time.perf_counter() - start_time

                if show_time:
                    print("Solve: %.3f. Parse: %.3f" % (solve_time, parse_time))


if __name__ == "__main__":
    unittest.main()
