## holpy

Implementation of higher-order logic in Python.

### Verification of symbolic integration:

See README file in the [`integral`](integral/) directory.

### Installation and usage:

This project requires Python 3.5 or greater and npm:

https://www.python.org/download/releases/3.0/:

https://www.npmjs.com/

Required packages are listed in requirements.txt. To install required packages in the
global environment, you can use:

```python -m pip install -r requirements.txt```

Depending on your system, may need to replace python by python3 or python3.x.

To avoid conflicts between projects that require different versions of packages,
we recommend installing Python packages in an isolated environment, e.g.
when using the `bash` shell, in the repository root directory do:

```
$ python3 -m venv ENV                 # Run python3.5 or above.
$ source ENV/bin/activate             # Sets up "python" to be your python3.
$ python -m pip install -r requirements.txt
$ python app.py                       # Runs the backend server on localhost:5000
```

In this same shell you can restore your previous environment later with

```$ deactivate```

The user interface is built using Vue, in the `./app` folder. To set up and
run the user interface server, in a different terminal
change to `./app` and use ```npm install``` followed by ```npm run serve```.

In your browser the user interface is at page `localhost:8080`.

To see statistics for the search functionality on a collection of lemmas, use:

```python -m server.collect_stat```

Unit tests for the backend are located in files of the form ```*/tests/*_test.py```.

### Directory structure:

* [`kernel`](kernel/): kernel for higher-order logic.
  * [`type`](kernel/type.py): datatype for HOL types.
  * [`term`](kernel/term.py): datatype for HOL terms.
  * [`thm`](kernel/thm.py): datatype for HOL theorems, including list of basic derivations.
  * [`proof`](kernel/proof.py): linear representation of a proof, consisting of a list of instructions to the kernel.
  * [`macro`](kernel/macro.py): macros as user-defined proof methods.
  * [`theory`](kernel/theory.py): theory state, containing signature for types and constants, and list of axioms and theorems.
  * [`extension`](kernel/extension.py): types of extensions to a theory.
  * [`report`](kernel/report.py): statistics and debugging information for checking a theory extension.

* [`logic`](logic/): base logic and standard automation.
  * [`matcher`](logic/matcher.py): matching of terms.
  * [`proofterm`](logic/proofterm.py): tree-like representation of a proof. Used for convenient construction of proofs, and can be transformed to the linear representation.
  * [`conv`](logic/conv.py): conversions.
  * [`logic`](logic/logic.py): utilities and definition of standard macros for logic.
  * [`basic`](logic/basic.py): functions for loading theories.

* [`data`](data/): common data types.
  * [`nat`](data/nat.py): natural numbers.
  * [`function`](data/function.py): functions.
  * [`list`](data/list.py): lists.
  * [`set`](data/set.py): sets.
  * [`real`](data/real.py): real numbers.

* [`syntax`](syntax/): parsing and printing.
  * [`operator`](syntax/operator.py): data for unary and binary operators.
  * [`infertype`](syntax/infertype.py): type inference.
  * [`printer`](syntax/printer.py): printing functions.
  * [`parser`](syntax/parser.py): parsing functions, built using Lark parser.

* [`server`](server/): toplevel functions.
  * [`server`](server/server.py): definition and standard operations for proof states.
  * [`tactic`](server/tactic.py): definition of tactics.
  * [`method`](server/method.py): definition of methods.

* [`app`](app/): web application.
  * [`__init__.py`](app/__init__.py): main server program.

* [`library`](library/): main library of theories.
