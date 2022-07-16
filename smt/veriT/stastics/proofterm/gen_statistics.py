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
    print("                               Experimental Result (%s)               " % filename)
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
    total_stat = total(theory_stats)
    print("%10s  %7s %7s  %7s %7s  %8s %8s %8s" % total_stat)

    for st in theory_stats:
        print(st[0], "    ", " & ".join(st[1:3]), "& & & & & &", " & ".join(st[3:]))


def total(stats):
    solved_num = [2124, 162, 86, 259, 575, 943, 548, 85, 4172, 52, 171, 415, 2851, 55, 7168, 10]
    # solved_num      = [int(s[1]) for s in stats]
    # solved_time     = [float(s[2]) for s in stats]
    solved_time = [0.64, 0.112, 1.236, 0.341, 7.809, 3.051, 7.698, 11.188, 1.725, 3.026, 8.563, 1.019, 0.708, 0.1, 0.558, 0.069]
    # print("solved_num", solved_num)
    # print("solved_time", solved_time)
    solved_time_sum = [a * b for a, b in zip(solved_num, solved_time)]
    avg_solved_time = sum(solved_time_sum) / sum(solved_num)
    recon_num       = [int(s[3]) for s in stats]
    recon_time      = [float(s[4]) for s in stats]
    recon_time_sum  = [a * b for a, b in zip(recon_num, recon_time)]
    avg_recon_time  = sum(recon_time_sum) / sum(recon_num)
    success_rate    = sum(recon_num)/sum(solved_num)
    timeout         = [float(s[-2][:-1]) / 100 for s in stats]
    timeout_sum     = [a * b for a, b in zip(solved_num, timeout)]
    avg_timeout     = sum(timeout_sum) / sum(solved_num)
    avg_r_time      = avg_recon_time / avg_solved_time
    return "Total", sum(solved_num), "%.3f" % avg_solved_time, sum(recon_num), \
                    "%.3f" % avg_recon_time, '{:.0%}'.format(success_rate), \
                        "{:.0%}".format(avg_timeout), "%.3f" % avg_r_time
