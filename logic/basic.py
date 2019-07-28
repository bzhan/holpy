# Author: Bohua Zhan

from copy import copy
import os
import inspect
import json

from kernel.theory import Theory
from logic import logic  # Load all defined macros
from data import expr
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

def load_json_data(theory_name, *, user="master"):
    """Load json data for the given theory name and user."""
    if user == "master":
        dir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
        with open(dir + '/../library/' + theory_name + '.json', encoding='utf-8') as a:
            return json.load(a)
    else:
        with open('users/' + user + '/' + theory_name + '.json', encoding='utf-8') as a:
            return json.load(a)

def load_imported_theory(imports, user="master"):
    """Load imported theory according to the imports field in data."""

    imports = tuple(imports)
    assert isinstance(imports, tuple) and all(isinstance(imp, str) for imp in imports), \
        "load_imported_theory"

    if (imports, user) in loaded_theories:
        return copy(loaded_theories[(imports, user)])

    thy = get_init_theory()
    finished = []

    def rec(theory_name):
        data = load_json_data(theory_name, user=user)
        for imp in data['imports']:
            if imp not in finished:
                rec(imp)

        parser.parse_extensions(thy, data['content'])
        finished.append(theory_name)

    for imp in imports:
        rec(imp)

    loaded_theories[(imports, user)] = thy

    return copy(thy)

def load_theory(theory_name, *, limit=None, user="master"):
    """Load the theory with the given theory name. Optional limit is
    a pair (ty, name) specifying the first item that should not
    be loaded.
    
    """
    data = load_json_data(theory_name, user=user)
    thy = load_imported_theory(data['imports'], user=user)

    # Take the portion of content up to (and not including) limit
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

    # Read data into theory
    parser.parse_extensions(thy, content)

    return thy

def clear_cache(user="master"):
    """Clear cached theories for the given user."""
    global loaded_theories
    loaded_theories = {k: v for k, v in loaded_theories.items() if k[1] != user}
