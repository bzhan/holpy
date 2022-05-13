import csv
import statistics

theories = [
    'AUFLIA',
    'LIA',
    'LRA',
    'QF_AUFLIA',
    'QF_IDL',
    'QF_LIA',
    'QF_LRA',
    'QF_RDL',
    'QF_UF',
    'QF_UFIDL',
    'QF_UFLIA',
    'QF_UFLRA',
    'UF',
    'UFIDL',
    'UFLIA',
    'UFLRA',
]

def collect_theory(filename, theory_name):
    rows = []
    with open(filename) as f:
        f_reader = csv.reader(f)
        _ = next(f_reader)
        for row in f_reader:
            th_name = row[0][11:].split("/")[0]
            if th_name == theory_name:
                rows.append(row)
    solved = [row for row in rows if row[1].replace('.','',1).isdigit()]
    solved_time = [float(row[1]) for row in solved]
    reconstructed_row = [row for row in solved if row[3].replace('.','',1).isdigit()]
    reconstructed_time = [float(row[2])+float(row[3]) for row in reconstructed_row]
    timeout_row = [row for row in solved if "Timeout" in row[3] or "Timeout" in row[2]]
    solve_num = str(len(solved))
    solve_avg_time = "%.3f" % statistics.mean(solved_time)
    recon_num = str(len(reconstructed_row))
    recon_avg_time = "%.3f" % statistics.mean(reconstructed_time)
    success = '{:.0%}'.format(len(reconstructed_row)/len(solved))
    to = '{:.0%}'.format(len(timeout_row)/len(solved))
    r_time = "%.2f" % (statistics.mean(reconstructed_time) / statistics.mean(solved_time))
    return theory_name, solve_num, solve_avg_time, recon_num, recon_avg_time, success, to, r_time

def display(filename):
    print("                               Experimental Result                                ")
    print("----------------------------------------------------------------------------------")
    print("%10s  %15s  %15s  %26s" % ('Theory', 'Solved (veriT)', 'Reconstruted', 'Rates'))
    print("----------------------------------------------------------------------------------")
    print("%10s  %7s %7s  %7s %7s  %8s %8s %8s" % ("", "#", "Time", "#", "Time", "Success", "Timeout", "R-time"))
    theory_stats = []
    for th in theories:
        theory_stats.append(collect_theory(filename, th))
    for st in theory_stats:
        print("%10s  %7s %7s  %7s %7s  %8s %8s %8s" % st)
    print("----------------------------------------------------------------------------------")

display("SMT-LIB.csv")
