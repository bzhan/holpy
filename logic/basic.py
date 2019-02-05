# Author: Bohua Zhan

from copy import copy
import json

from kernel.theory import Theory
from logic.operator import OperatorTable
from logic import logic_macro
from syntax import parser


"""Global record of loaded theories."""
loaded_theories = dict()


def loadTheory(name):
    """Load the theory with the given name."""
    # If the theory is already loaded, return the theory.
    if name in loaded_theories:
        return loaded_theories[name]

    # Otherwise, open the corresponding file.
    with open('library/' + name + '.json', encoding='utf-8') as a:
        data = json.load(a)

    if data['imports']:
        # Has at least one import
        if len(data['imports']) > 1:
            raise NotImplementedError

        thy = copy(loadTheory(data['imports'][0]))
        parser.parse_extensions(thy, data['content'])
        return thy
    else:
        # The root theory
        thy = Theory.EmptyTheory()

        # Operators
        thy.add_data_type("operator", OperatorTable())

        parser.parse_extensions(thy, data['content'])
        return thy


BasicTheory = loadTheory('logic_base')
