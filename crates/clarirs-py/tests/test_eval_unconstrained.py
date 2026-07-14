from __future__ import annotations

import unittest

import claripy


class TestEvalUnconstrained(unittest.TestCase):
    """Unconstrained bits of an evaluated expression default to zero.

    Z3's model completion fills variables absent from the model with zero, and
    eval reads the expression directly so that behavior is preserved (matching
    claripy). A previous implementation bound the value to an auxiliary
    variable, which pulled otherwise-free bits into the model with arbitrary
    values.
    """

    def test_fully_unconstrained_bv(self):
        x = claripy.BVS("x", 32)
        self.assertEqual(claripy.Solver().eval(x, 1)[0], 0)

    def test_partially_constrained_concat(self):
        b = [claripy.BVS(f"b_{i}", 8) for i in range(5)]
        expr = claripy.Concat(*b)
        s = claripy.Solver()
        s.add(b[0] == 0x41)
        s.add(b[1] == 0x42)
        # b[0], b[1] are pinned; b[2..4] are free and must come out as zero.
        self.assertEqual(s.eval(expr, 1)[0], 0x4142000000)

    def test_free_bits_zero_with_unrelated_constraints(self):
        # A free variable stays zero even when the solver carries constraints
        # over other variables.
        x = claripy.BVS("x", 16)
        y = claripy.BVS("y", 16)
        s = claripy.Solver()
        s.add(y == 0x1234)
        self.assertEqual(s.eval(x, 1)[0], 0)

    def test_batch_eval_zero_fills(self):
        b = [claripy.BVS(f"c_{i}", 8) for i in range(3)]
        expr = claripy.Concat(*b)
        s = claripy.Solver()
        s.add(b[1] == 0x7F)
        row = s.batch_eval([expr], 1)[0]
        self.assertEqual(row[0], 0x007F00)


if __name__ == "__main__":
    unittest.main()
