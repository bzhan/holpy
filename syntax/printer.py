# Author: Bohua Zhan

from copy import copy

from kernel.type import HOLType
from kernel import term
from kernel.term import Term, OpenTermException
from kernel.extension import Extension
from kernel import proof
from syntax import operator
from syntax import settings
from syntax import infertype
from syntax import pprint
from util import name

# 0, 1, 2, 3 = NORMAL, BOUND, VAR, TVAR
def N(s):
    return [(s, 0)] if settings.highlight() else s

def B(s):
    return [(s, 1)] if settings.highlight() else s

def V(s):
    return [(s, 2)] if settings.highlight() else s

def Gray(s):
    return [(s, 4)] if settings.highlight() else s

@settings.with_settings
def commas_join(strs):
    """Given a list of output (with or without highlight), join them with
    commas, adding commas with normal color in the highlight case.

    """
    strs = list(strs)  # convert possible generator to concrete list
    if settings.highlight():
        if strs:
            res = strs[0]
            for s in strs[1:]:
                res.append((', ', 0))
                res = res + s
            return res
        else:
            return []
    else:
        return ', '.join(strs)

@settings.with_settings
def print_type(thy, T):
    return pprint.print_type(thy, T)

@settings.with_settings
def print_term(thy, t, *, line_length=None):
    """More sophisticated printing function for terms. Handles printing
    of operators.
    
    Note we do not yet handle name collisions in lambda terms.

    """
    assert isinstance(t, Term), "print_term: input is not a term."

    ast = pprint.get_ast(thy, t)
    res = pprint.print_ast(thy, ast, line_length=line_length)
    return res

@settings.with_settings
def print_thm(thy, th):
    """Print the given theorem with highlight."""
    turnstile = N("⊢") if settings.unicode() else N("|-")
    if th.hyps:
        str_hyps = commas_join(print_term(thy, hyp) for hyp in th.hyps)
        return str_hyps + N(" ") + turnstile + N(" ") + print_term(thy, th.prop)
    else:
        return turnstile + N(" ") + print_term(thy, th.prop)

@settings.with_settings
def print_extension(thy, ext):
    if ext.ty == Extension.AX_TYPE:
        return "AxType " + ext.name + " " + str(ext.arity)
    elif ext.ty == Extension.AX_CONSTANT:
        return "AxConstant " + ext.name + " :: " + print_type(thy, ext.T)
    elif ext.ty == Extension.CONSTANT:
        return "Constant " + ext.name + " = " + print_term(thy, ext.expr)
    elif ext.ty == Extension.THEOREM:
        return "Theorem " + ext.name + ": " + print_term(thy, ext.th.prop)
    elif ext.ty == Extension.ATTRIBUTE:
        return "Attribute " + ext.name + " [" + ext.attribute + "]"
    elif ext.ty == Extension.MACRO:
        return "Macro " + ext.name
    else:
        raise TypeError

@settings.with_settings
def print_extensions(thy, exts):
    return "\n".join(print_extension(thy, ext) for ext in exts.data)

@settings.with_settings
def print_str_args(thy, rule, args, th):
    def str_val(val):
        if isinstance(val, dict):
            items = sorted(val.items(), key = lambda pair: pair[0])
            return N('{') + commas_join(N(key + ': ') + str_val(val) for key, val in items) + N('}')
        elif isinstance(val, Term):
            if th and val == th.prop and rule != 'assume' and settings.highlight():
                return Gray("⟨goal⟩")
            else:
                return print_term(thy, val)
        elif isinstance(val, HOLType):
            return print_type(thy, val)
        else:
            return N(str(val))

    # Print var :: T for variables
    if rule == 'variable' and settings.highlight():
        return N(args[0] + ' :: ') + str_val(args[1])

    if isinstance(args, tuple) or isinstance(args, list):
        return commas_join(str_val(val) for val in args)
    elif args:
        return str_val(args)
    else:
        return [] if settings.highlight() else ""

@settings.with_settings
def export_proof_item(thy, item):
    """Export the given proof item as a dictionary."""
    str_th = print_thm(thy, item.th, highlight=False) if item.th else ""
    str_args = print_str_args(thy, item.rule, item.args, item.th, highlight=False)
    res = {'id': proof.print_id(item.id), 'th': str_th, 'rule': item.rule,
           'args': str_args, 'prevs': [proof.print_id(prev) for prev in item.prevs]}
    if settings.highlight():
        res['th_hl'] = print_term(thy, item.th.prop) if item.th else ""
        res['args_hl'] = print_str_args(thy, item.rule, item.args, item.th)
    if item.subproof:
        return [res] + sum([export_proof_item(thy, i) for i in item.subproof.items], [])
    else:
        return [res]

@settings.with_settings
def print_proof_item(thy, item):
    """Print the given proof item."""
    str_id = proof.print_id(item.id)
    str_args = " " + print_str_args(thy, item.rule, item.args, item.th) if item.args else ""
    str_prevs = " from " + ", ".join(proof.print_id(prev) for prev in item.prevs) if item.prevs else ""
    str_th = print_thm(thy, item.th) + " by " if item.th else ""
    cur_line = str_id + ": " + str_th + item.rule + str_args + str_prevs
    if item.subproof:
        return cur_line + "\n" + "\n".join(print_proof_item(thy, item) for item in item.subproof.items)
    else:
        return cur_line

@settings.with_settings
def print_proof(thy, prf):
    """Print the given proof."""
    assert isinstance(prf, proof.Proof), "print_proof"
    return '\n'.join(print_proof_item(thy, item) for item in prf.items)

@settings.with_settings
def print_tyinst(thy, tyinst):
    """Print a type instantiation."""
    return "{" + ", ".join(nm + ": " + print_type(thy, T) for nm, T in sorted(tyinst.items())) + "}"

@settings.with_settings
def print_inst(thy, inst):
    """Print a term instantiation."""
    return "{" + ", ".join(nm + ": " + print_term(thy, t) for nm, t in sorted(inst.items())) + "}"

@settings.with_settings
def print_instsp(thy, instsp):
    """Print a pair of type and term instantiations."""
    tyinst, inst = instsp
    return print_tyinst(thy, tyinst) + ", " + print_inst(thy, inst)
