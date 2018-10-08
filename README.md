## holpy

Implementation of higher-order logic in Python.

This project is developed under Python 3.6.

Directory structure:

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
  * [`basic`](logic/basic.py): definition of base logic and standard proof methods.
  * [`matcher`](logic/matcher.py): matching of terms.
  * [`proofterm`](logic/proofterm.py): tree-like representation of a proof. Used for convenient construction of proofs, and can be transformed to the linear representation.
  * [`conv`](logic/conv.py): conversions.
