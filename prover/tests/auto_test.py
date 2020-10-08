"""Unit test for auto."""

import unittest

from logic import basic
from prover.auto import auto


class AutoTest(unittest.TestCase):
    def testOpenEmpty(self):
        basic.load_theory('topology')

        st = auto.init_proof_theorem('open_empty')
        st.step_for(10, debug=False)


if __name__ == "__main__":
    unittest.main()
