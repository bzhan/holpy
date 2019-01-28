# Author: Bohua Zhan

import io
import json
import os

from kernel.theory import Theory
from logic.operator import OperatorTable
from logic import logic_macro
from syntax import parser


def getBasicTheory():
    thy = Theory.EmptyTheory()

    # Operators
    thy.add_data_type("operator", OperatorTable())

    # Basic definitions and theorems
    script_dir = os.path.dirname(__file__)
    with io.open(os.path.join(script_dir, '..', 'library', 'logic_base.json'), encoding="utf-8") as a:
        data = json.load(a)

    parser.parse_extensions(thy, data)

    return thy

BasicTheory = getBasicTheory()
