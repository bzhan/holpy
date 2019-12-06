# Author: Bohua Zhan

from kernel.type import boolT
from kernel.term import Term

LEFT, RIGHT = range(2)
CONST, UNARY, BINARY = range(3)

class OperatorData():
    """Represents information for one operator.
    
    fun_name -- name of the corresponding function.
    priority -- operators with higher number will be evaluated first.
    assoc -- association to left (LEFT_ASSOC) or right (RIGHT_ASSOC).
    arity -- one of CONST, UNARY, or BINARY.
    ascii_op -- ascii text of the operator.
    unicode_op -- unicode text of the operator.

    """
    def __init__(self, fun_name, priority, *, assoc=None, arity=BINARY,
                 ascii_op, unicode_op=None, key=None):
        self.fun_name = fun_name
        self.priority = priority
        self.assoc = assoc
        self.arity = arity
        self.ascii_op = ascii_op
        if unicode_op is None:
            self.unicode_op = ascii_op
        else:
            self.unicode_op = unicode_op
        if key is None:
            self.key = self.fun_name
        else:
            self.key = key


class BinderData():
    """Represents information for one binder.
    
    fun_name -- name of the corresponding function.
    ascii_op -- ascii text of the operator.
    unicode_op -- unicode text of the operator.
    
    """
    def __init__(self, fun_name, *, ascii_op, unicode_op=None, key=None):
        self.fun_name = fun_name
        self.ascii_op = ascii_op
        if unicode_op is None:
            self.unicode_op = ascii_op
        else:
            self.unicode_op = unicode_op
        if key is None:
            self.key = self.fun_name
        else:
            self.key = key


op_data_raw = [
    OperatorData("equals", 50, assoc=LEFT, ascii_op="="),
    OperatorData("equals", 25, assoc=RIGHT, ascii_op="<-->", unicode_op="⟷", key="iff"),
    OperatorData("implies", 20, assoc=RIGHT, ascii_op="-->", unicode_op="⟶"),
    OperatorData("conj", 35, assoc=RIGHT, ascii_op="&", unicode_op="∧"),
    OperatorData("disj", 30, assoc=RIGHT, ascii_op="|", unicode_op="∨"),
    OperatorData("neg", 95, arity=UNARY, ascii_op="~", unicode_op="¬"),
    OperatorData("plus", 65, assoc=LEFT, ascii_op="+"),
    OperatorData("minus", 65, assoc=LEFT, ascii_op="-"),
    OperatorData("uminus", 95, arity=UNARY, ascii_op="-"),
    OperatorData("power", 81, assoc=LEFT, ascii_op="^"),
    OperatorData("times", 70, assoc=LEFT, ascii_op="*"),
    OperatorData("real_divide", 70, assoc=LEFT, ascii_op="/"),
    OperatorData("nat_divide", 70, assoc=LEFT, ascii_op="DIV"),
    OperatorData("nat_modulus", 70, assoc=LEFT, ascii_op="MOD"),
    OperatorData("less_eq", 50, assoc=LEFT, ascii_op="<=", unicode_op="≤"),
    OperatorData("less", 50, assoc=LEFT, ascii_op="<"),
    OperatorData("greater_eq", 50, assoc=LEFT, ascii_op=">=", unicode_op="≥"),
    OperatorData("greater", 50, assoc=LEFT, ascii_op=">"),
    OperatorData("zero", 0, arity=CONST, ascii_op="0"),
    OperatorData("append", 65, assoc=RIGHT, ascii_op="@"),
    OperatorData("cons", 65, assoc=RIGHT, ascii_op="#"),
    OperatorData("member", 50, assoc=LEFT, ascii_op="Mem", unicode_op="∈"),
    OperatorData("subset", 50, assoc=LEFT, ascii_op="Sub", unicode_op="⊆"),
    OperatorData("inter", 70, assoc=LEFT, ascii_op="Int", unicode_op="∩"),
    OperatorData("union", 65, assoc=LEFT, ascii_op="Un", unicode_op="∪"),
    OperatorData("empty_set", 0, arity=CONST, ascii_op="{}", unicode_op="∅"),
    OperatorData("Union", 95, arity=UNARY, ascii_op="UN ", unicode_op="⋃"),
    OperatorData("Inter", 95, arity=UNARY, ascii_op="INT ", unicode_op="⋂"),
    OperatorData("comp_fun", 60, assoc=RIGHT, ascii_op="O", unicode_op="∘"),
]

binder_data_raw = [
    BinderData("all", ascii_op="!", unicode_op="∀"),
    BinderData("exists", ascii_op="?", unicode_op="∃"),
    BinderData("exists1", ascii_op="?!", unicode_op="∃!"),
    BinderData("The", ascii_op="THE "),
]

op_data = dict()
for entry in op_data_raw:
    op_data[entry.key] = entry

binder_data = dict()
for entry in binder_data_raw:
    binder_data[entry.key] = entry

def get_info_for_fun(t):
    """Returns data associated to a function term. The result is None
    if the function is not found.

    """
    if t.is_const():
        if t.name == 'equals':
            Targs, _ = t.T.strip_type()
            if Targs[0] == boolT:
                return op_data['iff']
            else:
                return op_data['equals']
        else:
            if t.name in op_data:
                return op_data[t.name]
            else:
                return None
    else:
        return None

def get_binder_info_for_fun(t):
    """Returns data associated to a binder."""
    if t.is_const() and t.name in binder_data:
        return binder_data[t.name]
    else:
        return None
