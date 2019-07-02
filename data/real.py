# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Const

# Basic definitions

realT = Type("real")
plus = Const("real_plus", TFun(realT, realT, realT))
minus = Const("real_minus", TFun(realT, realT, realT))
uminus = Const("real_uminus", TFun(realT, realT))
times = Const("real_times", TFun(realT, realT, realT))
