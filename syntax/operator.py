# Author: Bohua Zhan

from kernel.type import boolT
from kernel.term import Term

class OperatorData():
    """Represents information for one operator."""
    
    LEFT_ASSOC, RIGHT_ASSOC = range(2)
    CONST, UNARY, BINARY = range(3)

    def __init__(self, fun_name, priority, *, assoc=None, arity=BINARY, ascii_op=None, unicode_op=None):
        """Instantiate data for an operator."""
        self.fun_name = fun_name
        self.priority = priority
        self.assoc = assoc
        self.arity = arity
        self.ascii_op = ascii_op
        self.unicode_op = unicode_op

class OperatorTable():
    """Represents information for operators.
    
    For each operator, we record its corresponding function, priority,
    and left/right associativity.
    
    """
    def __init__(self):
        LEFT, RIGHT = OperatorData.LEFT_ASSOC, OperatorData.RIGHT_ASSOC
        self.data = [
            OperatorData("equals", 50, assoc=LEFT, ascii_op="="),
            OperatorData("equals", 25, assoc=RIGHT, ascii_op="<-->", unicode_op="⟷"),
            OperatorData("implies", 25, assoc=RIGHT, ascii_op="-->", unicode_op="⟶"),
            OperatorData("conj", 35, assoc=RIGHT, ascii_op="&", unicode_op="∧"),
            OperatorData("disj", 30, assoc=RIGHT, ascii_op="|", unicode_op="∨"),
            OperatorData("neg", 40, arity=OperatorData.UNARY, ascii_op="~", unicode_op="¬"),
            OperatorData("plus", 65, assoc=LEFT, ascii_op="+"),
            OperatorData("times", 70, assoc=LEFT, ascii_op="*"),
            OperatorData("less_eq", 50, assoc=LEFT, ascii_op="<=", unicode_op="≤"),
            OperatorData("less", 50, assoc=LEFT, ascii_op="<"),
            OperatorData("zero", 0, arity=OperatorData.CONST, ascii_op="0"),
            OperatorData("append", 65, assoc=RIGHT, ascii_op="@"),
            OperatorData("cons", 65, assoc=RIGHT, ascii_op="#"),
            OperatorData("member", 50, assoc=LEFT, ascii_op="Mem", unicode_op="∈"),
            OperatorData("subset", 50, assoc=LEFT, ascii_op="Sub", unicode_op="⊆"),
            OperatorData("inter", 70, assoc=LEFT, ascii_op="Int", unicode_op="∩"),
            OperatorData("union", 65, assoc=LEFT, ascii_op="Un", unicode_op="∪"),
            OperatorData("empty_set", 0, arity=OperatorData.CONST, ascii_op="{}", unicode_op="∅"),
            OperatorData("Union", 90, arity=OperatorData.UNARY, ascii_op="UN ", unicode_op="⋃"),
            OperatorData("Inter", 90, arity=OperatorData.UNARY, ascii_op="INT ", unicode_op="⋂"),
            OperatorData("comp_fun", 60, assoc=RIGHT, ascii_op="O", unicode_op="∘"),
        ]


def get_info_for_fun(thy, t):
    """Returns data associated to a function term. The result is None
    if the function is not found.

    """
    LEFT, RIGHT = OperatorData.LEFT_ASSOC, OperatorData.RIGHT_ASSOC
    if t.is_const():
        if t.name == 'equals':
            Targs, _ = t.T.strip_type()
            if Targs[0] == boolT:
                return OperatorData("equals", 25, assoc=RIGHT, ascii_op="<-->", unicode_op="⟷")
            else:
                return OperatorData("equals", 50, assoc=LEFT, ascii_op="=")
        else:
            # First attempt to translate to general name
            name_lookup = thy.lookup_overload_const(t.name)
            for d in thy.get_data("operator").data:
                if d.fun_name == name_lookup:
                    return d

    return None
