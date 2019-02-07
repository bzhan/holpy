# Author: Bohua Zhan

from kernel.type import TVar, Type, TFun
from kernel.term import Const

"""Utility functions for lists."""

_Ta = TVar("a")
_Talist = Type("list", _Ta)

nil = Const("nil", _Talist)
cons = Const("cons", TFun(_Ta, _Talist, _Talist))
append = Const("append", TFun(_Talist, _Talist, _Talist))
