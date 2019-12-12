# Author: Bohua Zhan

from copy import copy

from kernel.type import HOLType
from kernel.term import Term, OpenTermException
from kernel.thm import Thm
from kernel import extension
from kernel import proof
from syntax import operator
from syntax import settings
from syntax import infertype
from syntax import pprint
from util import name
from util import typecheck


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
                res.extend(pprint.N(', '))
                res.extend(s)
            return res
        else:
            return []
    else:
        return ', '.join(strs)

@settings.with_settings
def print_type(thy, T):
    """Pretty-printing for types."""
    typecheck.checkinstance('print_type', T, HOLType)

    ast = pprint.get_ast_type(thy, T)
    return pprint.print_ast(thy, ast)

@settings.with_settings
def print_term(thy, t, *, line_length=None):
    """Pretty-printing for terms."""
    typecheck.checkinstance('print_term', t, Term)

    ast = pprint.get_ast_term(thy, t)
    return pprint.print_ast(thy, ast, line_length=line_length)

@settings.with_settings
def print_thm(thy, th):
    """Print the given theorem with highlight."""
    typecheck.checkinstance('print_thm', th, Thm)

    turnstile = pprint.N("⊢") if settings.unicode() else pprint.N("|-")
    if th.hyps:
        str_hyps = commas_join(print_term(thy, hyp) for hyp in th.hyps)
        return str_hyps + pprint.N(" ") + turnstile + pprint.N(" ") + print_term(thy, th.prop)
    else:
        return turnstile + pprint.N(" ") + print_term(thy, th.prop)

@settings.with_settings
def print_extension(thy, ext):
    typecheck.checkinstance('print_extension', ext, extension.Extension)
    if ext.ty == extension.TYPE:
        return "Type " + ext.name + " " + str(ext.arity)
    elif ext.ty == extension.CONSTANT:
        ref_str = " (" + ext.ref_name + ")" if ext.ref_name != ext.name else ""
        return "Constant " + ext.name + " :: " + print_type(thy, ext.T) + ref_str
    elif ext.ty == extension.THEOREM:
        return "Theorem " + ext.name + ": " + print_term(thy, ext.th.prop)
    elif ext.ty == extension.ATTRIBUTE:
        return "Attribute " + ext.name + " [" + ext.attribute + "]"
    elif ext.ty == extension.OVERLOAD:
        return "Overload " + ext.name
    else:
        raise TypeError

@settings.with_settings
def print_extensions(thy, exts):
    typecheck.checkinstance('print_extensions', exts, [extension.Extension])
    return "\n".join(print_extension(thy, ext) for ext in exts)

@settings.with_settings
def print_type_constr(thy, constr):
    """Print a given type constructor."""
    argsT, _ = constr['type'].strip_type()
    assert len(argsT) == len(constr['args']), "print_type_constr: unexpected number of args."
    res = pprint.N(constr['name'])
    for i, arg in enumerate(constr['args']):
        res += pprint.N(' (' + arg + ' :: ') + print_type(thy, argsT[i]) + pprint.N(')')
    return res

@settings.with_settings
def print_str_args(thy, rule, args, th):
    def str_val(val):
        if isinstance(val, dict):
            items = sorted(val.items(), key = lambda pair: pair[0])
            return pprint.N('{') + commas_join(pprint.N(key + ': ') + str_val(val)
                                               for key, val in items) + pprint.N('}')
        elif isinstance(val, Term):
            if th and val == th.prop and rule != 'assume' and settings.highlight():
                return pprint.Gray("⟨goal⟩")
            else:
                return print_term(thy, val)
        elif isinstance(val, HOLType):
            return print_type(thy, val)
        else:
            return pprint.N(str(val))

    # Print var :: T for variables
    if rule == 'variable' and settings.highlight():
        return pprint.N(args[0] + ' :: ') + str_val(args[1])

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
    res = {'id': str(item.id), 'th': str_th, 'rule': item.rule,
           'args': str_args, 'prevs': [str(prev) for prev in item.prevs]}
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
    str_id = str(item.id)
    str_args = " " + print_str_args(thy, item.rule, item.args, item.th) if item.args else ""
    str_prevs = " from " + ", ".join(str(prev) for prev in item.prevs) if item.prevs else ""
    str_th = print_thm(thy, item.th) + " by " if item.th else ""
    cur_line = str_id + ": " + str_th + item.rule + str_args + str_prevs
    if item.subproof:
        return cur_line + "\n" + "\n".join(print_proof_item(thy, item) for item in item.subproof.items)
    else:
        return cur_line

@settings.with_settings
def print_proof(thy, prf):
    """Print the given proof."""
    typecheck.checkinstance('print_proof', prf, proof.Proof)
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
