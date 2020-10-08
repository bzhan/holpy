"""Unit test for auto."""

import unittest

from logic import basic
from prover.auto import auto


class AutoTest(unittest.TestCase):
    def testOpenEmpty(self):
        basic.load_theory('topology')

        st = auto.init_proof_theorem('open_empty')
        st.step_for(20, debug=False)
        self.assertEqual(st.step_count, 7)
        self.assertEqual(len(st.updates), 6)


if __name__ == "__main__":
    unittest.main()
