# Author: Bohua Zhan

from copy import copy
from typing import Tuple
import contextlib

from kernel.type import Type, TVar, TFun, BoolType, TypeMatchException
from kernel.term import Term, Var, TypeCheckException
from kernel.thm import Thm, primitive_deriv, InvalidDerivationException
from kernel.proof import Proof, ProofStateException
from kernel.macro import ProofMacro, has_macro, get_macro
from kernel import extension
from kernel.report import ExtensionReport


class TheoryException(Exception):
    """General exception for theory operations."""
    def __init__(self, str):
        self.str = str

class CheckProofException(Exception):
    """Exception when checking proof. Provides error message."""
    def __init__(self, str):
        self.str = str

class ParameterQueryException(Exception):
    """Represents an exception that is raised when a method need
    to ask for additional parameters. The list of parameters is
    contained in the list params.

    """
    def __init__(self, params):
        assert isinstance(params, list) and all(isinstance(param, str) for param in params), \
            "ParameterQueryException: input is not a list of strings"
        self.params = params

class Theory():
    """Represents the current state of the theory.

    Data contained in the theory include the following:

    type_sig: type signature. The arity of each type constant.

    term_sig: term signature. The most general type of each term constant.

    theorems: list of currently proved theorems.

    One can also define new kinds of data to be kept in the theory.

    The data in the theory is contained in the dictionary self.data.
    The keys of self.data are strings indicating the type of data.
    The corresponding values are dictionaries by default, but can be
    objects of any class in general.

    Theory object is also responsible for proof checking. Parameters for
    proof checking include:

    Theory object can be extended by a theory extension, which contains
    a list of new types, constants, and theorems to add to a theory.
    Theory object is responsible for checking all proofs in a theory
    extension.

    """
    def __init__(self):
        self.data = dict()

    def __copy__(self):
        """Creates a shallow copy of the current theory. This is defined
        as performing a shallow copy on all values on self.data.

        """
        res = Theory()
        res.data = dict()
        for name, val in self.data.items():
            res.data[name] = copy(val)
        return res

    def add_data_type(self, name, init = None):
        """Add a new data type.
        
        init - initial data. Default value is dict().
        
        """
        if name in self.data:
            raise TheoryException("Add data type")
        
        if init is None:
            init = dict()
        self.data[name] = init

    def add_data(self, name, key, val):
        """Add the given key-value pair to the data for the given data
        type. This can be used to modify theory data of dictionary type only.
        
        """
        if name not in self.data:
            raise TheoryException("Add data")

        assert isinstance(self.data[name], dict), "add_data: data must be a dictionary"

        self.data[name][key] = val

    def update_data(self, name, f):
        """Update data for the given data type with the function f. This
        can be used to update theory data that is not a dictionary.
        
        f is applied to the current data, and the output of f becomes the
        new data.
        
        """
        if name not in self.data:
            raise TheoryException("Update data")

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
            raise TheoryException("Type " + name + " not found")

        return data[name]

    def add_term_sig(self, name, T):
        """Add to the term signature. The constant term with the given name
        is defined in the theory with the given most general type.

        """
        if self.is_overload_const(name):
            # Assert the given type is an instance of the overloaded type,
            # and all instantiations are concrete types.
            aT = self.get_term_sig(name, stvar=True)
            try:
                inst = aT.match(T)
            except TypeMatchException:
                raise TheoryException("Constant %s :: %s does not match overloaded type %s" % (name, T, aT))

            for _, v in sorted(inst.items()):
                if not v.is_tconst():
                    raise TheoryException("When overloading %s with %s: cannot instantiate to type variables" % (aT, T))
        else:
            # Make sure this name does not already occur in the theory
            if self.has_term_sig(name):
                raise TheoryException("Constant %s already exists" % name)

            self.add_data("term_sig", name, T)

    def has_term_sig(self, name):
        return name in self.get_data("term_sig")

    def get_term_sig(self, name, stvar=False):
        """Returns the most general type of the term."""
        data = self.get_data("term_sig")
        if name not in data:
            raise TheoryException("Const " + name + " not found")

        if stvar:
            return data[name].convert_stvar()
        else:
            return data[name]

    def add_theorem(self, name, th):
        """Add the given theorem under the given name."""
        if not isinstance(th, Thm):
            raise TypeError

        self.add_data("theorems", name, th)

    def has_theorem(self, name):
        """Returns whether the current theory contains the given theorem."""
        data = self.get_data("theorems")
        return name in data
    
    def get_theorem(self, name, svar=False):
        """Returns the theorem under that name."""
        data = self.get_data("theorems")
        if name not in data:
            raise TheoryException("Theorem " + name + " not found")

        if svar:
            data_svar = self.get_data("theorems_svar")
            if name not in data_svar:
                data_svar[name] = Thm.convert_svar(data[name])
            return data_svar[name]
        else:
            return data[name]

    def add_attribute(self, name, attribute):
        """Add an attribute for the given theorem."""
        old_attributes = tuple()
        if name in self.data['attributes']:
            old_attributes = self.data['attributes'][name]
        self.data['attributes'][name] = old_attributes + (attribute,)

    def get_attributes(self, name):
        """Get the list of attributes for the given theorem."""
        if name in self.data['attributes']:
            return self.data['attributes'][name]
        else:
            return tuple()

    def add_overload_const(self, name):
        """Add a constant as an overloaded constant."""
        data = self.get_data("overload")
        data[name] = True

    def is_overload_const(self, name):
        """Whether the given name is an overloaded constant."""
        data = self.get_data("overload")
        return name in data

    def get_overload_const_name(self, name, T):
        """Obtain the full name of the overloaded constant.
        
        Input is the general constant name and the type of the constant.
        Types will be appended to the front of the name, separated by
        underscores.

        For example:
        (plus, nat => nat => nat) returns nat_plus.
        (power, real => nat => real) returns real_nat_power.

        """
        if self.is_overload_const(name):
            aT = self.get_term_sig(name, stvar=True)
            try:
                inst = aT.match(T)
            except TypeMatchException:
                raise TheoryException("Constant %s :: %s does not match overloaded type %s" % (name, T, aT))

            baseT = []
            for _, v in sorted(inst.items()):
                if v.is_tconst():
                    baseT.append(v)

            T_name = "_".join(T.name for T in baseT)
            return T_name + "_" + name
        else:
            return name

    def check_type(self, T):
        """Check the well-formedness of the type T. This means checking
        that all type constructors exist and are instantiated with the right
        arity.

        """
        if T.is_stvar() or T.is_tvar():
            return None
        elif T.is_tconst():
            if not self.has_type_sig(T.name):
                raise TheoryException("Unknown type %s" % T.name)        
            if self.get_type_sig(T.name) != len(T.args):
                raise TheoryException("Incorrect arity for type %s" % T.name)
            for arg in T.args:
                self.check_type(arg)
        else:
            raise TypeError

    def check_term(self, t):
        """Check the well-formedness of the term t. This means checking
        that all constant terms exist and have the right type according to
        the theory.

        """
        if t.is_var():
            return None
        elif t.is_const():
            try:
                self.get_term_sig(t.name, stvar=True).match(t.T)
            except TypeMatchException:
                raise TheoryException("Check term: " + repr(t))
        elif t.is_comb():
            self.check_term(t.fun)
            self.check_term(t.arg)
        elif t.is_abs():
            self.check_term(t.body)
        elif t.is_bound():
            return None
        else:
            raise TypeError

    def _check_proof_item(self, prf, seq, rpt, no_gaps, compute_only, check_level):
        """Check a single proof item.

        prf -- proof to be checked.
        seq -- proof item to be checked.
        rpt -- report for proof-checking. Modified by the function.
        no_gaps -- disable gaps.
        compute_only -- only executes rule if theorem is not present.
        check_level -- trust level for proof checking. Trust all macros
            with macro.level <= self.check_level.
        
        """
        if seq.rule == "":
            # Empty line in the proof
            return None

        if seq.rule == "sorry":
            # Gap in the proof
            assert seq.th is not None, "sorry must have explicit statement."
            if no_gaps:
                raise CheckProofException("gaps are not allowed")
            if rpt is not None:
                rpt.add_gap(seq.th)
            return None

        if compute_only and seq.th is not None:
            # In compute_only mode, skip when a theorem exists. However,
            # subproofs still need to be checked.
            if seq.rule == "subproof":
                for s in seq.subproof.items:
                    self._check_proof_item(prf, s, rpt, no_gaps, compute_only, check_level)
            return None

        if seq.rule == "theorem":
            # Copies an existing theorem in the theory into the proof.
            try:
                res_th = self.get_theorem(seq.args, svar=True)
                if rpt is not None:
                    rpt.apply_theorem(seq.args)
            except TheoryException:
                raise CheckProofException("theorem not found")
        elif seq.rule == "variable":
            # Declares a variable. Skip check.
            nm, T = seq.args
            res_th = Thm.mk_VAR(Var(nm, T))
        elif seq.rule == "subproof":
            for s in seq.subproof.items:
                self._check_proof_item(prf, s, rpt, no_gaps, compute_only, check_level)
            res_th = seq.subproof.items[-1].th
        else:
            # Otherwise, apply one of the proof methods. First, we
            # obtain list of previous sequents used by the proof method:
            prev_ths = []
            assert isinstance(seq.prevs, list), "prevs should be a list"
            for prev in seq.prevs:
                if not seq.id.can_depend_on(prev):
                    raise CheckProofException("id %s cannot depend on %s" % (seq.id, prev))
                try:
                    prev_ths.append(prf.find_item(prev).th)
                except ProofStateException:
                    raise CheckProofException("previous item not found")
            
            for prev, prev_th in zip(seq.prevs, prev_ths):
                if prev_th is None:
                    raise CheckProofException("previous theorem %s is None" % prev)

            if seq.rule in primitive_deriv:
                # If the method is one of the primitive derivations, obtain and
                # apply that primitive derivation.
                rule_fun, _ = primitive_deriv[seq.rule]
                try:
                    res_th = rule_fun(*prev_ths) if seq.args is None else rule_fun(seq.args, *prev_ths)
                    if rpt is not None:
                        rpt.apply_primitive_deriv()
                except InvalidDerivationException:
                    raise CheckProofException("invalid derivation")
                except TypeError:
                    raise CheckProofException("invalid input to derivation " + seq.rule)

            elif has_macro(seq.rule):
                # Otherwise, the proof method corresponds to a macro. If
                # the level of the macro is less than or equal to the current
                # trust level, simply evaluate the macro to check that results
                # match. Otherwise, expand the macro and check all of the steps.
                macro = get_macro(seq.rule)
                assert macro.level is None or (isinstance(macro.level, int) and macro.level >= 0), \
                    ("check_proof: invalid macro level " + str(macro.level))
                if macro.level is not None and macro.level <= check_level:
                    res_th = macro.eval(seq.args, prev_ths)
                    if rpt is not None:
                        rpt.eval_macro(seq.rule)
                else:
                    seq.subproof = macro.expand(seq.id, seq.args, list(zip(seq.prevs, prev_ths)))
                    if rpt is not None:
                        rpt.expand_macro(seq.rule)
                    for s in seq.subproof.items:
                        self._check_proof_item(prf, s, rpt, no_gaps, compute_only, check_level)
                    res_th = seq.subproof.items[-1].th
                    seq.subproof = None
            else:
                raise CheckProofException("proof method not found: " + seq.rule)

        if seq.th is None:
            # No expected theorem is provided
            seq.th = res_th
        elif not res_th.can_prove(seq.th):
            # Resulting res_th is OK as long as the conclusion is the same,
            # and the assumptions is a subset of that of seq.th.
            raise CheckProofException("output does not match\n" + str(seq.th) + "\n vs.\n" + str(res_th))

        # Check the current statement is correctly typed.
        try:
            seq.th.check_thm_type()
        except TypeCheckException:
            raise CheckProofException("typing error")

        return None

    def check_proof(self, prf, rpt=None, *, no_gaps=False, compute_only=False, check_level=0):
        """Verify the given proof object. Returns the final theorem if check
        passes. Otherwise throws CheckProofException.

        prf -- proof to be checked.
        rpt -- report for proof-checking. Modified by the function.
        
        """
        assert isinstance(prf, Proof), "check_proof"
        for seq in prf.items:
            self._check_proof_item(prf, seq, rpt, no_gaps, compute_only, check_level)

        return prf.items[-1].th

    def get_proof_rule_sig(self, name):
        """Obtain the argument signature of the proof rule."""
        if name == "theorem":
            return str
        elif name == "variable":
            return Tuple[str, Type]
        elif name == "sorry" or name == "subproof":
            return None
        elif name in primitive_deriv:
            _, sig = primitive_deriv[name]
            return sig
        else:
            macro = get_macro(name)
            return macro.sig

    def extend_type(self, ext):
        """Extend the theory by adding a type."""
        assert ext.is_tconst(), "extend_type"

        self.add_type_sig(ext.name, ext.arity)

    def extend_constant(self, ext):
        """Extend the theory by adding a constant."""
        assert ext.is_constant(), "extend_constant"

        self.add_term_sig(ext.name, ext.T)

    def extend_attribute(self, ext):
        """Extend the theory by adding an attribute."""
        assert ext.is_attribute(), "extend_attribute"

        self.add_attribute(ext.name, ext.attribute)

    def unchecked_extend(self, exts):
        """Perform the given theory extension without proof checking."""
        for ext in exts:
            if ext.is_tconst():
                self.extend_type(ext)
            elif ext.is_constant():
                self.extend_constant(ext)
            elif ext.is_theorem():
                self.add_theorem(ext.name, ext.th)
            elif ext.is_attribute():
                self.extend_attribute(ext)
            elif ext.is_overload():
                self.add_overload_const(ext.name)
            else:
                raise TypeError

    def checked_extend(self, exts):
        """Perform the given theory extension with proof checking."""
        ext_report = ExtensionReport()

        for ext in exts:
            if ext.is_tconst():
                self.extend_type(ext)
            elif ext.is_constant():
                self.extend_constant(ext)
            elif ext.is_theorem():
                if ext.prf:
                    self.check_proof(ext.prf)
                else:  # No proof - add as axiom
                    ext_report.add_axiom(ext.name, ext.th)

                self.add_theorem(ext.name, ext.th)
            elif ext.is_attribute():
                self.extend_attribute(ext)
            elif ext.is_overload():
                self.add_overload_const(ext.name)
            else:
                raise TypeError

        return ext_report


"""Global theory"""
thy = None

def EmptyTheory():
    """Empty theory, with the absolute minimum setup."""
    thy = Theory()

    # Fundamental data structures, needed for proof checking.
    thy.add_data_type("type_sig")
    thy.add_data_type("term_sig")
    thy.add_data_type("theorems")
    thy.add_data_type("theorems_svar")  # cache of version of theorem with SVar.
    thy.add_data_type("attributes")
    thy.add_data_type("overload")

    # Fundamental types.
    thy.add_type_sig("bool", 0)
    thy.add_type_sig("fun", 2)

    # Fundamental terms.
    thy.add_term_sig("equals", TFun(TVar("a"), TVar("a"), BoolType))
    thy.add_term_sig("implies", TFun(BoolType, BoolType, BoolType))
    thy.add_term_sig("all", TFun(TFun(TVar("a"), BoolType), BoolType))
    
    return thy

@contextlib.contextmanager
def fresh_theory():
    # Record previous theory
    global thy
    prev_thy = thy

    # Set theory to empty
    thy = EmptyTheory()
    try:
        yield None
    finally:
        # Recover previous theory
        thy = prev_thy


global_methods = dict()

def has_method(name):
    if name in global_methods:
        method = global_methods[name]
        return method.limit is None or thy.has_theorem(method.limit)
    else:
        return False

def get_method(name):
    assert has_method(name), "get_method: %s is not available" % name
    return global_methods[name]

def get_all_methods():
    res = dict()
    for name in global_methods:
        if has_method(name):
            res[name] = global_methods[name]
    return res

def get_method_sig():
    sig = dict()
    for name in global_methods:
        if has_method(name):
            sig[name] = global_methods[name].sig
    return sig


class Method:
    """Methods represent potential actions on the state."""
    def search(self, state, id, prevs):
        pass

    def apply(self, state, id, args, prevs):
        pass
