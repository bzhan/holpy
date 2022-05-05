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

import csv

test_files = open('test_files.txt', 'w')
summary = open('summary.txt', 'w')

summary.write("%10s%10s\n" % ('Theory', 'Count'))
summary.write("--------------------\n")

total_count = 0
for name in theories:
    filename = name + '.csv'
    count = 0
    with open(filename, newline='') as csvfile:
        reader = csv.reader(csvfile, delimiter=',', quotechar='|')
        for row in reader:
            assert len(row) <= 2
            if len(row) == 2 and row[1] == 'RETURN PROOF':
                filename = row[0]
                assert row[0].split('/')[0] == name
                test_files.write(filename + '\n')
                count += 1
                total_count += 1
        summary.write("%10s%10s\n" % (name, count))

summary.write("--------------------\n")
summary.write("%10s%10s\n" % ('Total', total_count))

test_files.close()
summary.close()
