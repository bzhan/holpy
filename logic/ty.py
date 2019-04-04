'''
from logic import logic, induct
from kernel.type import TVar, Type, TFun, hol_bool
from kernel.term import Var, Const, Term
from kernel.thm import Thm
from kernel.extension import AxType, AxConstant, Theorem, Attribute
from logic import logic, induct

Ta = TVar("a")
Tlista = Type("list", Ta)
list_ext = induct.add_induct_type(
            "list", ["a"], [("nil", Tlista, []), ("cons", TFun(Ta, Tlista, Tlista), ["x", "xs"])])

print(list_ext.data)
'''