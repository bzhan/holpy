import csv
import os

theories = [
    "QF_UF", 
    "QF_UFLRA", 
    "QF_UFLIA", 
    "QF_UFIDL", 
    "UF", 
    "UFLRA", 
    "UFLIA", 
    "QF_LRA", 
    "QF_AUFLIA", 
    "AUFLIA", 
    "LRA", 
    "LIA", 
    "QF_LIA"
]

test_files = open('test_files.txt', 'w')
summary = open('summary.txt', 'w')

summary.write("%15s%10s\n" % ('Theory', 'Count'))
summary.write("-------------------------------\n")

total_count = 0
for name in theories:
    smt_files = os.listdir(name)
    count = len(smt_files)
    for smt_file in smt_files:
        test_files.write(name+"/"+smt_file+"\n")
    summary.write("%15s%10s\n" % (name, count))
    total_count += count
summary.write("-------------------------------\n")
summary.write("%15s%10s\n" % ('Total', total_count))

test_files.close()
summary.close()