# Author: Bohua Zhan

import abc
from kernel.type import *
from kernel.term import *
from kernel.thm import *
from kernel.macro import *
from kernel.extension import *
from kernel.report import *

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

    def add_proof_macro(self, name, macro):
        """Add the given proof macro."""
        if not isinstance(macro, ProofMacro):
            raise TheoryException()

        self.add_data("proof_macro", name, macro)

    def has_proof_macro(self, name):
        """Whether the given name corresponds to a proof macro."""
        data = self.get_data("proof_macro")
        return name in data

    def get_proof_macro(self, name):
        """Returns the proof macro with that name."""
        data = self.get_data("proof_macro")
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

    def get_check_level(self):
        """Returns the trust level for the proof checking. Trust all macros
        with macro.level <= self.check_level.

        """
        if hasattr(self, "check_level"):
            return self.check_level
        else:
            return 0

    def _check_proof_item(self, depth, seq_dict, seq):
        """Check a single proof item.
        
        depth -- depth in macro expansion.
        seq_dict -- dictionary of existing sequents.
        
        """
        # First, check the current statement is correctly typed.
        try:
            seq.th.check_thm_type()
        except TypeCheckException:
            raise CheckProofException("typing error")

        if seq.rule == "theorem":
            # Copies an existing theorem in the theory into the proof.
            try:
                res_th = self.get_theorem(seq.args)
            except TheoryException:
                raise CheckProofException("theorem not found")
        else:
            # Otherwise, apply one of the proof methods. First, we
            # obtain list of previous sequents used by the proof method:
            prev_ths = []
            assert isinstance(seq.prevs, list), "prevs should be a list"
            for prev in seq.prevs:
                if prev not in seq_dict:
                    raise CheckProofException("previous item not found")
                else:
                    prev_ths.append(seq_dict[prev])

            # Next, obtain list of arguments to pass in:
            if seq.args is not None:
                args = [seq.args]
            else:
                args = []

            if seq.rule in base_deriv:
                # If the method is one of the base derivations, obtain and
                # apply that base derivation.
                rule_fun = base_deriv[seq.rule]
                try:
                    res_th = rule_fun(*prev_ths, *args)
                except InvalidDerivationException:
                    raise CheckProofException("invalid derivation")
                except TypeError:
                    raise CheckProofException("invalid input to derivation " + seq.rule)

            elif self.has_proof_macro(seq.rule):
                # Otherwise, the proof method corresponds to a macro. If
                # the level of the macro is less than or equal to the current
                # trust level, simply evaluate the macro to check that results
                # match. Otherwise, expand the macro and check all of the steps.
                macro = self.get_proof_macro(seq.rule)
                if macro.level <= self.get_check_level():
                    res_th = macro.eval(*prev_ths, *args)
                else:
                    prf = macro.expand(depth+1, seq.prevs, *prev_ths, *args)
                    res_th = self.check_proof_incr(depth+1, seq_dict.copy(), prf)
            else:
                raise CheckProofException("proof method not found")

        if seq.th != res_th:
            raise CheckProofException("output does not match\n" + str(seq.th) + "\n vs.\n" + str(res_th))

        seq_dict[seq.id] = seq.th
        return None

    def check_proof_incr(self, depth, seq_dict, prf):
        """Incremental version of check_proof.
        
        depth -- depth in macro expansion.
        
        seq_dict -- dictionary of existing sequents.
        
        """
        for seq in prf.get_items():
            self._check_proof_item(depth, seq_dict, seq)
        return prf.get_thm()

    def check_proof(self, prf):
        """Verify the given proof object. Returns the final theorem if check
        passes. Otherwise throws CheckProofException.
        
        """
        return self.check_proof_incr(0, dict(), prf)

    def extend_axiom_constant(self, ext):
        assert ext.ty == Extension.AX_CONSTANT, "extend_axiom_constant"

        self.add_term_sig(ext.name, ext.T)

    def extend_constant(self, ext):
        assert ext.ty == Extension.CONSTANT, "extend_constant"

        const = ext.get_const_term()
        self.add_term_sig(const.name, const.T)
        self.add_theorem(const.name + "_def", ext.get_eq_thm())

    def unchecked_extend(self, thy_ext):
        """Perform the given extension without checking any proofs."""
        for ext in thy_ext.get_extensions():
            if ext.ty == Extension.AX_CONSTANT:
                self.extend_axiom_constant(ext)
            elif ext.ty == Extension.CONSTANT:
                self.extend_constant(ext)
            elif ext.ty == Extension.THEOREM:
                self.add_theorem(ext.name, ext.th)
            else:
                raise UnknownExtensionException()

    def checked_extend(self, thy_ext):
        """Perform the given extension, checking all proofs."""
        ext_report = ExtensionReport()

        for ext in thy_ext.get_extensions():
            if ext.ty == Extension.AX_CONSTANT:
                self.extend_axiom_constant(ext)
                ext_report.add_axiom(ext.name, ext.T)
            elif ext.ty == Extension.CONSTANT:
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
