#__autuor__: "zhouwenfan"
# coding= utf-8
#date: 2018/12/12

from syntax.parser import *
from logic.basic import BasicTheory
import json,sys,io
from syntax.printer import *

sys.stdout = io.TextIOWrapper(sys.stdout.buffer,encoding='gb18030')
thy = BasicTheory
with open('logic/basic.json', 'r', encoding='utf-8') as f:
    data1 = json.load(f)
    print(data1)
for d in data1:
    term = parse_extension(thy, d)
    if term:
        m = print_term(thy, term, highlight=True)
        print(m)
