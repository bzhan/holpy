# Author: Bohua Zhan

from kernel.type import Type, TFun
from kernel.term import Const

# Basic definitions

realT = Type("real")
plus = Const("real_plus", TFun(realT, realT, realT))
times = Const("real_times", TFun(realT, realT, realT))
