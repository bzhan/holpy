# Author: Bohua Zhan

from copy import copy
import os
import inspect
import json

from kernel.theory import Theory
from logic import logic_macro  # Load all defined macros
from data import expr
from logic import hoare
from syntax import parser
from syntax import operator
from server import method  # Load all defined methods

"""Global record of loaded theories."""
loaded_theories = dict()


def get_init_theory():
    """Returns a (fresh copy of) the initial theory. This is an
    extension of EmptyTheory, adding only the operator data field.

    """
    # The root theory
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", operator.OperatorTable())

    return thy

def load_imported_theory(imports, user=""):
    """Load imported theory according to the imports field in data."""
    if imports:
        # Has at least one import
        if len(imports) > 1:
            raise NotImplementedError

        return copy(load_theory(imports[0], user=user))
    else:
        return get_init_theory()

def load_theory(theory_name, *, limit=None, user=""):
    """Load the theory with the given theory name. Optional limit is
    a pair (ty, name) specifying the first item that should not
    be loaded.
    
    """
    # If the theory is already loaded, return the theory.
    if limit is None and (theory_name, user) in loaded_theories:
        return loaded_theories[(theory_name, user)]

    # Otherwise, open the corresponding file.
    if user == "":
        dir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
        with open(dir + '/../library/' + theory_name + '.json', encoding='utf-8') as a:
            data = json.load(a)
    else:
        with open('users/' + user + '/' + theory_name + '.json', encoding='utf-8') as a:
            data = json.load(a)

    content = data['content']
    limit_i = -1
    if limit:
        ty, name = limit
        for i, val in enumerate(content):
            if val['ty'] == ty and val['name'] == name:
                limit_i = i
                break
        assert limit_i != -1, "Limit not found"
        content = content[:limit_i]

    thy = load_imported_theory(data['imports'], user=user)
    parser.parse_extensions(thy, content)

    if limit is None:
        loaded_theories[(theory_name, user)] = thy

    return thy

def clear_cache(user=""):
    """Clear cached theories for the given user."""
    global loaded_theories
    loaded_theories = {k: v for k, v in loaded_theories.items() if k[1] != user}
