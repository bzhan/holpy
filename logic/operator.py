# Author: Bohua Zhan

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
            OperatorData("implies", 25, assoc=RIGHT, ascii_op="-->", unicode_op="⟶"),
            OperatorData("conj", 35, assoc=RIGHT, ascii_op="&", unicode_op="∧"),
            OperatorData("disj", 30, assoc=RIGHT, ascii_op="|", unicode_op="∨"),
            OperatorData("neg", 40, arity=OperatorData.UNARY, ascii_op="~", unicode_op="¬"),
            OperatorData("plus", 65, assoc=LEFT, ascii_op="+"),
            OperatorData("times", 70, assoc=LEFT, ascii_op="*"),
            OperatorData("zero", 0, arity=OperatorData.CONST, ascii_op="0"),
            OperatorData("append", 65, assoc=RIGHT, ascii_op="@"),
            OperatorData("cons", 65, assoc=RIGHT, ascii_op="#"),
        ]

    def get_info_for_fun(self, t):
        """Returns data associated to a function term. The result is None
        if the function is not found.

        """
        if t.is_const():
            for d in self.data:
                if d.fun_name == t.name:
                    return d

        return None
