# Author: Bohua Zhan

import abc
from kernel.type import *
from kernel.term import *
from kernel.thm import *
from kernel.extension import *

class TheoryException(Exception):
    pass

class CheckProofException(Exception):
    """Exception when checking proof. Provides error message."""
    def __init__(self, str):
        self.str = str

class Theory(abc.ABC):
    """Theory objects contain all information about the current theory.

    The data of the theory is structured as a dictionary. The keys are
    strings indicating the type of the data. The values are the dictionary
    for that type of data.

    """
    def __init__(self):
        self.data = dict()

    def add_data_type(self, name):
        """Add a new data type."""
        if name in self.data:
            raise TheoryException()
        
        self.data[name] = dict()

    def get_data(self, name):
        return self.data[name]

    def add_data(self, name, key, val):
        """Apply key:val to the current data."""
        if name not in self.data:
            raise TheoryException()

        self.data[name][key] = val

    def add_type_sig(self, name, n):
        """Add to the type signature. The type constructor with the given name
        is associated to arity n.

        """
        self.add_data("type_sig", name, n)

    def get_type_sig(self, name):
        """Returns the arity of the type."""
        data = self.get_data("type_sig")
        if name not in data:
            raise TheoryException()

        return data[name]

    def add_term_sig(self, name, T):
        """Add to the term signature. The constant term with the given name
        is defined in the theory with the given most general type.

        """
        self.add_data("term_sig", name, T)

    def get_term_sig(self, name):
        """Returns the most general type of the term."""
        data = self.get_data("term_sig")
        if name not in data:
            raise TheoryException()

        return data[name]

    def add_theorem(self, name, th):
        """Add the given theorem under the given name."""
        if not isinstance(th, Thm):
            raise TheoryException()

        self.add_data("theorems", name, th)
    
    def get_theorem(self, name):
        """Returns the theorem under that name."""
        data = self.get_data("theorems")
        if name not in data:
            raise TheoryException()

        return data[name]

    @staticmethod
    def EmptyTheory():
        """Empty theory, with the absolute minimum setup."""
        thy = Theory()

        # Fundamental data structures, needed for proof checking.
        thy.add_data_type("type_sig")
        thy.add_data_type("term_sig")
        thy.add_data_type("theorems")
        thy.add_data_type("term_macro")
        thy.add_data_type("proof_macro")

        # Fundamental types.
        thy.add_type_sig("bool", 0)
        thy.add_type_sig("fun", 2)

        # Fundamental terms.
        thy.add_term_sig("equals", TFun(TVar("a"), TFun(TVar("a"), hol_bool)))
        thy.add_term_sig("implies", TFun(hol_bool, TFun(hol_bool, hol_bool)))
        
        return thy

    def check_type(self, T):
        """Check the well-formedness of the type T. This means checking
        that all type constructors exist and are instantiated with the right
        arity.

        """
        if T.ty == HOLType.VAR:
            return None
        elif T.ty == HOLType.COMB:
            if self.get_type_sig(T.name) != len(T.args):
                raise TheoryException()
            else:
                for arg in T.args:
                    self.check_type(arg)
        else:
            raise UnknownTypeException()

    def check_term(self, t):
        """Check the well-formedness of the term t. This means checking
        that all constant terms exist and have the right type according to
        the theory.

        """
        if t.ty == Term.VAR:
            return None
        elif t.ty == Term.CONST:
            try:
                self.get_term_sig(t.name).match(t.T)
            except TypeMatchException:
                raise TheoryException()
        elif t.ty == Term.COMB:
            self.check_term(t.fun)
            self.check_term(t.arg)
        elif t.ty == Term.ABS:
            self.check_term(t.body)
        elif t.ty == Term.BOUND:
            return None
        else:
            raise UnknownTermException()

    def check_proof(self, prf):
        """Verify the given proof object. Returns the final theorem if check
        passes. Otherwise throws CheckProofException.
        
        """
        # Map from id to already seen sequents.
        seq_dict = dict()

        for seq in prf.get_items():
            try:
                seq.th.check_thm_type()
            except TypeCheckException:
                raise CheckProofException("typing error")

            if seq.rule == "theorem":
                try:
                    res_th = self.get_theorem(seq.args)
                except TheoryException:
                    raise CheckProofException("theorem not found")
            else:
                if seq.rule not in base_deriv:
                    raise CheckProofException("proof method not found")

                rule_fun = base_deriv[seq.rule]

                # Obtain list of previous sequents.
                prev_ths = []
                if seq.prevs:
                    assert isinstance(seq.prevs, list), "prevs should be None or a list"
                    for prev in seq.prevs:
                        if prev not in seq_dict:
                            raise CheckProofException("previous item not found")
                        else:
                            prev_ths.append(seq_dict[prev])

                # Obtain list of arguments to pass in
                if seq.args:
                    args = [seq.args]
                else:
                    args = []

                try:
                    res_th = rule_fun(*prev_ths, *args)
                except InvalidDerivationException:
                    raise CheckProofException("invalid derivation")
                except TypeError:
                    raise CheckProofException("invalid input to derivation")

            if seq.th != res_th:
                raise CheckProofException("output does not match")

            seq_dict[seq.id] = seq.th

        return prf.get_thm()

    def extend_constant(self, ext):
        assert ext.ty == Extension.CONSTANT, "extend_constant"

        const = ext.get_const_term()
        self.add_term_sig(const.name, const.T)
        self.add_theorem(const.name + "_def", ext.get_eq_thm())

    def unchecked_extend(self, thy_ext):
        """Perform the given extension without checking any proofs."""
        for ext in thy_ext.get_extensions():
            if ext.ty == Extension.CONSTANT:
                self.extend_constant(ext)
            elif ext.ty == Extension.THEOREM:
                self.add_theorem(ext.name, ext.th)
            else:
                raise UnknownExtensionException()

    def checked_extend(self, thy_ext):
        """Perform the given extension, checking all proofs."""
        ext_report = ExtensionReport()

        for ext in thy_ext.get_extensions():
            if ext.ty == Extension.CONSTANT:
                self.extend_constant(ext)
            elif ext.ty == Extension.THEOREM:
                if ext.prf:
                    self.check_proof(ext.prf)
                else:  # No proof - add as axiom
                    ext_report.add_axiom(ext.name, ext.th)

                self.add_theorem(ext.name, ext.th)
            else:
                raise UnknownExtensionException()

        return ext_report
