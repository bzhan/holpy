# Author: Bohua Zhan

from copy import copy

from kernel import type as hol_type
from kernel.type import Type
from kernel import term
from kernel.term import Term, Inst
from kernel.thm import Thm
from kernel import extension
from kernel import proof
from syntax import operator
from syntax.settings import settings, global_setting
from syntax import infertype
from syntax import pprint
from util import name
from util import typecheck


def commas_join(strs):
    """Given a list of output (with or without highlight), join them with
    commas, adding commas with normal color in the highlight case.

    """
    strs = list(strs)  # convert possible generator to concrete list
    if settings.highlight:
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

def print_type(T):
    """Pretty-printing for types."""
    typecheck.checkinstance('print_type', T, Type)

    ast = pprint.get_ast_type(T)
    with global_setting(line_length=None):
        return pprint.print_ast(ast)

def print_term(t):
    """Pretty-printing for terms."""
    typecheck.checkinstance('print_term', t, Term)

    ast = pprint.get_ast_term(t)
    return pprint.print_ast(ast)

def print_thm(th):
    """Print the given theorem with highlight."""
    typecheck.checkinstance('print_thm', th, Thm)

    turnstile = pprint.N("⊢") if settings.unicode else pprint.N("|-")
    if th.hyps:
        str_hyps = commas_join(print_term(hyp) for hyp in th.hyps)
        return str_hyps + pprint.N(" ") + turnstile + pprint.N(" ") + print_term(th.prop)
    else:
        return turnstile + pprint.N(" ") + print_term(th.prop)

def print_extension(ext):
    typecheck.checkinstance('print_extension', ext, extension.Extension)
    if ext.is_tconst():
        return "Type " + ext.name + " " + str(ext.arity)
    elif ext.is_constant():
        ref_str = " (" + ext.ref_name + ")" if ext.ref_name != ext.name else ""
        return "Constant " + ext.name + " :: " + print_type(ext.T) + ref_str
    elif ext.is_theorem():
        return "Theorem " + ext.name + ": " + print_term(ext.th.prop)
    elif ext.is_attribute():
        return "Attribute " + ext.name + " [" + ext.attribute + "]"
    elif ext.is_overload():
        return "Overload " + ext.name
    else:
        raise TypeError

def print_extensions(exts):
    typecheck.checkinstance('print_extensions', exts, [extension.Extension])
    return "\n".join(print_extension(ext) for ext in exts)

def print_type_constr(constr):
    """Print a given type constructor."""
    argsT, _ = constr['type'].strip_type()
    assert len(argsT) == len(constr['args']), "print_type_constr: unexpected number of args."
    res = pprint.N(constr['name'])
    for i, arg in enumerate(constr['args']):
        res += pprint.N(' (' + arg + ' :: ') + print_type(argsT[i]) + pprint.N(')')
    return res

def print_str_args(rule, args, th):
    def str_val(val):
        if isinstance(val, Inst):
            items = sorted(val.items(), key = lambda pair: pair[0])
            return pprint.N('{') + commas_join(pprint.N(key + ': ') + str_val(val)
                                               for key, val in items) + pprint.N('}')
        elif isinstance(val, Term):
            if th and val == th.prop and rule != 'assume' and settings.highlight:
                return pprint.Gray("⟨goal⟩")
            else:
                return print_term(val)
        elif isinstance(val, Type):
            return print_type(val)
        else:
            return pprint.N(str(val))

    # Print var :: T for variables
    if rule == 'variable' and settings.highlight:
        return pprint.N(args[0] + ' :: ') + str_val(args[1])

    if isinstance(args, tuple) or isinstance(args, list):
        return commas_join(str_val(val) for val in args)
    elif args:
        return str_val(args)
    else:
        return [] if settings.highlight else ""

def export_proof_item(item):
    """Export the given proof item as a dictionary."""
    with global_setting(highlight=False):
        str_th = print_thm(item.th) if item.th else ""
        str_args = print_str_args(item.rule, item.args, item.th)
    res = {'id': str(item.id), 'th': str_th, 'rule': item.rule,
           'args': str_args, 'prevs': [str(prev) for prev in item.prevs]}
    if settings.highlight:
        res['th_hl'] = print_term(item.th.prop) if item.th else ""
        res['args_hl'] = print_str_args(item.rule, item.args, item.th)
    if item.subproof:
        return [res] + sum([export_proof_item(i) for i in item.subproof.items], [])
    else:
        return [res]

def print_proof_item(item):
    """Print the given proof item."""
    str_id = str(item.id)
    str_args = " " + print_str_args(item.rule, item.args, item.th) if item.args else ""
    str_prevs = " from " + ", ".join(str(prev) for prev in item.prevs) if item.prevs else ""
    str_th = print_thm(item.th) + " by " if item.th else ""
    cur_line = str_id + ": " + str_th + item.rule + str_args + str_prevs
    if item.subproof:
        return cur_line + "\n" + "\n".join(print_proof_item(item) for item in item.subproof.items)
    else:
        return cur_line

def print_proof(prf):
    """Print the given proof."""
    typecheck.checkinstance('print_proof', prf, proof.Proof)
    return '\n'.join(print_proof_item(item) for item in prf.items)


# Set up default printing functions
hol_type.type_printer = print_type
term.term_printer = print_term
