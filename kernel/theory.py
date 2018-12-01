# Author: Bohua Zhan

from kernel.type import HOLType, TVar, TFun, hol_bool, TypeMatchException
from kernel.term import Term, TypeCheckException
from kernel.thm import Thm, primitive_deriv, InvalidDerivationException
from kernel.macro import MacroSig, ProofMacro
from kernel.extension import Extension
from kernel.report import ExtensionReport

class TheoryException(Exception):
    pass

class CheckProofException(Exception):
    """Exception when checking proof. Provides error message."""
    def __init__(self, str):
        self.str = str

class Theory():
    """Represents the current state of the theory.

    Data contained in the theory include the following:

    type_sig: type signature. The arity of each type constant.

    term_sig: term signature. The most general type of each term constant.

    theorems: list of currently proved theorems.

    proof_macro: list of macros for abbreviating proofs.

    One can also define new kinds of data to be kept in the theory.

    The data in the theory is contained in the dictionary self.data.
    The keys of self.data are strings indicating the type of data.
    The corresponding values are dictionaries by default, but can be
    objects of any class in general.

    Theory object is also responsible for proof checking. Parameters for
    proof checking include:

    check_level -- trust level for proof checking. Trust all macros
    with macro.level <= self.check_level.

    Theory object can be extended by a theory extension, which contains
    a list of new types, constants, and theorems to add to a theory.
    Theory object is responsible for checking all proofs in a theory
    extension.

    """
    def __init__(self):
        self.data = dict()
        self.check_level = 0

    def add_data_type(self, name, init = None):
        """Add a new data type.
        
        init - initial data. Default value is dict().
        
        """
        if name in self.data:
            raise TheoryException()
        
        if init is None:
            init = dict()
        self.data[name] = init

    def add_data(self, name, key, val):
        """Add the given key-value pair to the data for the given data
        type. This can be used to modify theory data of dictionary type only.
        
        """
        if name not in self.data:
            raise TheoryException()

        assert isinstance(self.data[name], dict), "add_data: data must be a dictionary"

        self.data[name][key] = val

    def update_data(self, name, f):
        """Update data for the given data type with the function f. This
        can be used to update theory data that is not a dictionary.
        
        f is applied to the current data, and the output of f becomes the
        new data.
        
        """
        if name not in self.data:
            raise TheoryException()

        self.data[name] = f(self.data[name])

    def get_data(self, name):
        """Returns data for the given data type."""
        return self.data[name]

    def add_type_sig(self, name, n):
        """Add to the type signature. The type constructor with the given name
        is associated to arity n.

        """
        self.add_data("type_sig", name, n)

    def has_type_sig(self, name):
        return name in self.get_data("type_sig")

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

    def has_term_sig(self, name):
        return name in self.get_data("term_sig")

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
        thy.add_term_sig("equals", TFun(TVar("a"), TVar("a"), hol_bool))
        thy.add_term_sig("implies", TFun(hol_bool, hol_bool, hol_bool))
        thy.add_term_sig("all", TFun(TFun(TVar("a"), hol_bool), hol_bool))
        
        return thy

    def check_type(self, T):
        """Check the well-formedness of the type T. This means checking
        that all type constructors exist and are instantiated with the right
        arity.

        """
        if T.ty == HOLType.TVAR:
            return None
        elif T.ty == HOLType.TYPE:
            if self.get_type_sig(T.name) != len(T.args):
                raise TheoryException()
            else:
                for arg in T.args:
                    self.check_type(arg)
        else:
            raise TypeError()

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
            raise TypeError()

    def _check_proof_item(self, depth, seq_dict, seq, rpt):
        """Check a single proof item.
        
        depth -- depth in macro expansion.
        seq_dict -- dictionary of existing sequents.
        seq -- proof item to be checked.
        rpt -- report for proof-checking. Modified by the function.
        
        """
        if seq.rule == "":
            # Empty line in the proof
            return None
        if seq.rule == "sorry":
            # Gap in the proof
            assert seq.th is not None, "sorry must have explicit statement."
            res_th = seq.th
            if rpt is not None:
                rpt.add_gap(seq.th)
        elif seq.rule == "theorem":
            # Copies an existing theorem in the theory into the proof.
            try:
                res_th = self.get_theorem(seq.args)
                if rpt is not None:
                    rpt.apply_theorem(seq.args)
            except TheoryException:
                raise CheckProofException("theorem not found")
        else:
            # Otherwise, apply one of the proof methods. First, we
            # obtain list of previous sequents used by the proof method:
            prev_ths = []
            assert isinstance(seq.prevs, list), "prevs should be a list"
            for prev in seq.prevs:
                if prev not in seq_dict:
                    raise CheckProofException("previous item not found: " + str(prev))
                else:
                    prev_ths.append(seq_dict[prev])

            # Next, obtain list of arguments to pass in:
            if seq.args is not None:
                args = [seq.args]
            else:
                args = []

            if seq.rule in primitive_deriv:
                # If the method is one of the primitive derivations, obtain and
                # apply that primitive derivation.
                rule_fun, _ = primitive_deriv[seq.rule]
                try:
                    res_th = rule_fun(*(args + prev_ths))
                    if rpt is not None:
                        rpt.apply_primitive_deriv()
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
                args = [self] + args if macro.has_theory else args
                if macro.level <= self.check_level:
                    res_th = macro(*(args + prev_ths))
                    if rpt is not None:
                        rpt.eval_macro(seq.rule)
                else:
                    prf = macro.expand(depth+1, *(args + list(zip(seq.prevs, prev_ths))))
                    if rpt is not None:
                        rpt.expand_macro(seq.rule)
                    res_th = self.check_proof_incr(depth+1, seq_dict.copy(), prf, rpt)
            else:
                raise CheckProofException("proof method not found: " + seq.rule)

        if seq.th is None:
            # No expected theorem is provided
            seq.th = res_th
        elif seq.th != res_th:
            raise CheckProofException("output does not match\n" + str(seq.th) + "\n vs.\n" + str(res_th))

        # Check the current statement is correctly typed.
        try:
            seq.th.check_thm_type()
        except TypeCheckException:
            raise CheckProofException("typing error")

        seq_dict[seq.id] = seq.th
        return None

    def check_proof_incr(self, depth, seq_dict, prf, rpt = None):
        """Incremental version of check_proof.
        
        depth -- depth in macro expansion.
        seq_dict -- dictionary of existing sequents.
        prf -- proof to be checked.
        rpt -- report for proof-checking. Modified by the function.
        
        """
        for seq in prf.get_items():
            self._check_proof_item(depth, seq_dict, seq, rpt)
        return prf.get_thm()

    def check_proof(self, prf, rpt = None):
        """Verify the given proof object. Returns the final theorem if check
        passes. Otherwise throws CheckProofException.

        prf -- proof to be checked.
        rpt -- report for proof-checking. Modified by the function.
        
        """
        return self.check_proof_incr(0, dict(), prf, rpt)

    def get_proof_rule_sig(self, name):
        """Obtain the argument signature of the proof rule."""
        if name == "theorem":
            return MacroSig.STRING
        elif name == "sorry":
            return MacroSig.NONE
        elif name in primitive_deriv:
            _, sig = primitive_deriv[name]
            return sig
        else:
            macro = self.get_proof_macro(name)
            return macro.sig

    def extend_axiom_constant(self, ext):
        """Extend the theory by adding an axiomatic constant."""
        assert ext.ty == Extension.AX_CONSTANT, "extend_axiom_constant"

        self.add_term_sig(ext.name, ext.T)

    def extend_constant(self, ext):
        """Extend the theory by adding a constant, which is set to be
        equal to a certain expression.

        """
        assert ext.ty == Extension.CONSTANT, "extend_constant"

        const = ext.get_const_term()
        self.add_term_sig(const.name, const.T)
        self.add_theorem(const.name + "_def", ext.get_eq_thm())

    def unchecked_extend(self, thy_ext):
        """Perform the given theory extension without proof checking."""
        for ext in thy_ext.get_extensions():
            if ext.ty == Extension.AX_CONSTANT:
                self.extend_axiom_constant(ext)
            elif ext.ty == Extension.CONSTANT:
                self.extend_constant(ext)
            elif ext.ty == Extension.THEOREM:
                self.add_theorem(ext.name, ext.th)
            else:
                raise TypeError()

    def checked_extend(self, thy_ext):
        """Perform the given theory extension with proof checking."""
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
                raise TypeError()

        return ext_report
