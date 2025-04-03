from __future__ import annotations

import unittest

import clarirs as claripy
from clarirs.fp import FSORT_FLOAT, RM


class TestFPOperations(unittest.TestCase):
    def setUp(self):
        # Create concrete FP values for testing
        self.fp1 = claripy.FPV(1.5, FSORT_FLOAT)
        self.fp2 = claripy.FPV(2.5, FSORT_FLOAT)
        self.fp_zero = claripy.FPV(0.0, FSORT_FLOAT)
        self.fp_neg = claripy.FPV(-1.5, FSORT_FLOAT)
        self.fp_neg_zero = claripy.FPV(-0.0, FSORT_FLOAT)
        self.fp_inf = claripy.FPV(float("inf"), FSORT_FLOAT)
        self.fp_neg_inf = claripy.FPV(float("-inf"), FSORT_FLOAT)
        self.fp_nan = claripy.FPV(float("nan"), FSORT_FLOAT)
        # Add a subnormal number
        self.fp_subnormal = claripy.FPV(1e-40, FSORT_FLOAT)

        self.z3 = claripy.solver.SolverZ3()
        self.concrete = claripy.solver.SolverConcrete()

    def _check_equal(self, expr, expected):
        """Helper to check equality of FP expressions"""
        z3_result = self.z3.eval(expr, 1)[0]
        self.assertEqual(z3_result, expected, "Z3 result does not match expected value")

        if expr.symbolic:
            with self.assertRaises(claripy.ClaripyOperationError):
                self.concrete.eval(expr, 1)[0]
        else:
            concrete_result = self.concrete.eval(expr, 1)[0]
            self.assertEqual(concrete_result, expected, "Concrete result does not match expected value")

    def test_add(self):
        """Test addition operation"""
        rm = RM.default()
        # Test regular addition
        result = claripy.fpAdd(rm, self.fp1, self.fp2)
        self._check_equal(result, 4.0)

        # Test addition with zero
        result = claripy.fpAdd(rm, self.fp1, self.fp_zero)
        self._check_equal(result, 1.5)

    def test_sub(self):
        """Test subtraction operation"""
        rm = RM.default()
        # Test regular subtraction
        result = claripy.fpSub(rm, self.fp2, self.fp1)
        self._check_equal(result, 1.0)

        # Test subtraction resulting in zero
        result = claripy.fpSub(rm, self.fp1, self.fp1)
        self._check_equal(result, 0.0)

    def test_mul(self):
        """Test multiplication operation"""
        rm = RM.default()
        # Test regular multiplication
        result = claripy.fpMul(rm, self.fp1, self.fp2)
        self._check_equal(result, 3.75)

        # Test multiplication with zero
        result = claripy.fpMul(rm, self.fp1, self.fp_zero)
        self._check_equal(result, 0.0)

    def test_div(self):
        """Test division operation"""
        rm = RM.default()
        # Test regular division
        result = claripy.fpDiv(rm, self.fp2, self.fp1)
        # FIXME: claripy pretends everything is f64
        # self._check_equal(result, 1.6666666269302368)

        # Test division by zero - should result in infinity
        result = claripy.fpDiv(rm, self.fp1, self.fp_zero)
        self.assertTrue(claripy.fpIsInf(result).is_true())

        # Test division by negative zero - should result in negative infinity
        result = claripy.fpDiv(rm, self.fp1, self.fp_neg_zero)
        self.assertTrue(claripy.fpIsInf(result).is_true())
        # For negative zero division, we need to check if the result is negative infinity
        self.assertTrue(claripy.fpIsInf(claripy.fpNeg(result)).is_true())

        # Test infinity division
        result = claripy.fpDiv(rm, self.fp_inf, self.fp2)
        self.assertTrue(claripy.fpIsInf(result).is_true())

        # Test zero divided by zero - should be NaN
        result = claripy.fpDiv(rm, self.fp_zero, self.fp_zero)
        # FIXME: claripy doesn't do this correctly
        # self.assertTrue(claripy.fpIsNaN(result).is_true())

    def test_neg(self):
        """Test negation"""
        result = claripy.fpNeg(self.fp1)
        self._check_equal(result, -1.5)

    def test_abs(self):
        """Test absolute value"""
        result = claripy.fpAbs(self.fp_neg)
        self._check_equal(result, 1.5)

    def test_eq(self):
        """Test equality"""
        # Test equality with same value
        result = self.fp1 == self.fp1
        self._check_equal(result, True)

        # Test equality with different values
        result = self.fp1 == self.fp2
        self._check_equal(result, False)

    def test_ne(self):
        """Test inequality"""
        # Test inequality with different values
        result = self.fp1 != self.fp2
        self._check_equal(result, True)

        # Test inequality with same value
        result = self.fp1 != self.fp1
        self._check_equal(result, False)

    def test_lt(self):
        """Test less than"""
        result = claripy.fpLT(self.fp1, self.fp2)
        self._check_equal(result, True)

        result = claripy.fpLT(self.fp2, self.fp1)
        self._check_equal(result, False)

    def test_le(self):
        """Test less than or equal"""
        result = claripy.fpLEQ(self.fp1, self.fp2)
        self._check_equal(result, True)

        result = claripy.fpLEQ(self.fp1, self.fp1)
        self._check_equal(result, True)

    def test_gt(self):
        """Test greater than"""
        result = claripy.fpGT(self.fp2, self.fp1)
        self._check_equal(result, True)

        result = claripy.fpGT(self.fp1, self.fp2)
        self._check_equal(result, False)

    def test_ge(self):
        """Test greater than or equal"""
        result = claripy.fpGEQ(self.fp2, self.fp1)
        self._check_equal(result, True)

        result = claripy.fpGEQ(self.fp1, self.fp1)
        self._check_equal(result, True)

    def test_sqrt(self):
        """Test square root operation"""
        rm = RM.default()
        # Test regular square root
        result = claripy.fpSqrt(rm, self.fp1)
        self._check_equal(result, 1.2247449159622192)  # exact sqrt(1.5) from Z3

        # Test square root of zero
        result = claripy.fpSqrt(rm, self.fp_zero)
        self._check_equal(result, 0.0)

        # Test square root of negative - should be NaN
        result = claripy.fpSqrt(rm, self.fp_neg)
        self.assertTrue(self.z3.eval(claripy.fpIsNaN(result), 1)[0])

        # Test square root of infinity
        result = claripy.fpSqrt(rm, self.fp_inf)
        self.assertTrue(claripy.fpIsInf(result).is_true())

    def test_special_values(self):
        """Test operations with special values (NaN, Infinity, Subnormal)"""
        # Test NaN comparisons and propagation
        self.assertTrue(claripy.fpIsNaN(self.fp_nan).is_true())
        result = self.fp_nan == self.fp1
        self._check_equal(result, False)
        result = self.fp_nan != self.fp1
        self._check_equal(result, True)

        # Test NaN propagation in operations
        rm = RM.default()
        ops = [
            lambda x, y: claripy.fpAdd(rm, x, y),
            lambda x, y: claripy.fpSub(rm, x, y),
            lambda x, y: claripy.fpMul(rm, x, y),
            lambda x, y: claripy.fpDiv(rm, x, y),
        ]
        for op in ops:
            result = op(self.fp_nan, self.fp1)
            self.assertTrue(claripy.fpIsNaN(result).is_true())
            result = op(self.fp1, self.fp_nan)
            self.assertTrue(claripy.fpIsNaN(result).is_true())

        # Test Infinity comparisons and operations
        self.assertTrue(claripy.fpIsInf(self.fp_inf).is_true())
        result = claripy.fpGT(self.fp_inf, self.fp1)
        self._check_equal(result, True)
        result = claripy.fpLT(self.fp_neg_inf, self.fp1)
        self._check_equal(result, True)

        # Test operations with infinities
        result = claripy.fpAdd(rm, self.fp_inf, self.fp_inf)
        self.assertTrue(claripy.fpIsInf(result).is_true())
        self.assertFalse(claripy.fpLT(result, self.fp_zero).is_true())

        result = claripy.fpAdd(rm, self.fp_inf, self.fp_neg_inf)
        self.assertTrue(claripy.fpIsNaN(result).is_true())

        result = claripy.fpMul(rm, self.fp_inf, self.fp_neg_inf)
        self.assertTrue(claripy.fpIsInf(result).is_true())
        self.assertTrue(claripy.fpLT(result, self.fp_zero).is_true())

        # Test subnormal numbers
        self.assertTrue(claripy.fpLT(self.fp_subnormal, self.fp1).is_true())
        result = claripy.fpAdd(rm, self.fp_subnormal, self.fp_subnormal)
        self.assertTrue(claripy.fpLT(result, self.fp1).is_true())

        # Test operations mixing subnormal and normal numbers
        result = claripy.fpAdd(rm, self.fp_subnormal, self.fp1)
        self._check_equal(result, 1.5)  # subnormal is so small it doesn't affect 1.5

    @unittest.skip("claripy does not properly implement roundng modes for concrete values")
    def test_rounding_modes(self):
        """Test operations with different rounding modes"""
        # Test addition with different rounding modes
        # Use values that will produce different results with different rounding modes
        value = claripy.FPV(1.5, FSORT_FLOAT)
        value2 = claripy.FPV(0.2, FSORT_FLOAT)

        result_rne = claripy.fpAdd(RM.RM_NearestTiesEven, value, value2)
        result_rtz = claripy.fpAdd(RM.RM_TowardsZero, value, value2)
        result_rtp = claripy.fpAdd(RM.RM_TowardsPositiveInf, value, value2)
        result_rtn = claripy.fpAdd(RM.RM_TowardsNegativeInf, value, value2)

        # Check that rounding towards positive infinity gives larger result
        self.assertTrue(claripy.fpGT(result_rtp, result_rtz).is_true())
        # Check that rounding towards negative infinity gives smaller result
        self.assertTrue(claripy.fpLT(result_rtn, result_rtz).is_true())

    def test_reverse_ops(self):
        """Test reverse operations"""
        rm = RM.default()
        # Test reverse add
        value = claripy.FPV(2.0, FSORT_FLOAT)
        result = claripy.fpAdd(rm, value, self.fp1)
        expected = claripy.fpAdd(rm, value, self.fp1)
        self._check_equal(result, self.z3.eval(expected, 1)[0])

        # Test reverse subtract
        result = claripy.fpSub(rm, value, self.fp1)
        expected = claripy.fpSub(rm, value, self.fp1)
        self._check_equal(result, self.z3.eval(expected, 1)[0])

    def test_symbolic(self):
        """Test operations with symbolic variables"""
        rm = RM.default()
        # Create symbolic variables
        sym_x = claripy.FPS("x", FSORT_FLOAT)
        sym_y = claripy.FPS("y", FSORT_FLOAT)

        # Test basic operations
        result = claripy.fpAdd(rm, sym_x, self.fp1)
        self.assertTrue(result.symbolic)

        # Test comparisons
        result = claripy.fpLT(sym_x, sym_y)
        self.assertTrue(result.symbolic)

        # Test special value checks
        result = claripy.fpIsNaN(sym_x)
        self.assertTrue(result.symbolic)
        result = claripy.fpIsInf(sym_x)
        self.assertTrue(result.symbolic)

        # Test conversions
        double_sym = sym_x.to_fp(claripy.FSORT_DOUBLE)
        self.assertTrue(double_sym.symbolic)
        self.assertEqual(double_sym.sort.length, 64)

        # Test operations mixing symbolic and concrete
        concrete = claripy.FPV(1.5, FSORT_FLOAT)
        result = claripy.fpAdd(rm, sym_x, concrete)
        self.assertTrue(result.symbolic)

    def test_conversions(self):
        """Test FP conversion operations"""
        rm = RM.default()
        # Test fpToFP from FP
        double_val = self.fp1.to_fp(claripy.FSORT_DOUBLE)
        self.assertEqual(double_val.sort.length, 64)

        # Test conversion of special values
        inf_double = self.fp_inf.to_fp(claripy.FSORT_DOUBLE)
        self.assertTrue(claripy.fpIsInf(inf_double).is_true())

        nan_double = self.fp_nan.to_fp(claripy.FSORT_DOUBLE)
        self.assertTrue(claripy.fpIsNaN(nan_double).is_true())

        # Test fpToIEEEBV and back
        bv = self.fp1.to_bv()
        self.assertEqual(bv.length, 32)  # FSORT_FLOAT is 32 bits

        # Test fpToSBV/fpToUBV with different sizes
        for size in [16, 32, 64]:
            sbv = self.fp1.val_to_bv(size, signed=True)
            ubv = self.fp1.val_to_bv(size, signed=False)
            self.assertEqual(sbv.length, size)
            self.assertEqual(ubv.length, size)

        # Test conversion of special values to BV
        inf_bv = self.fp_inf.to_bv()
        neg_inf_bv = self.fp_neg_inf.to_bv()
        self.assertNotEqual(self.z3.eval(inf_bv, 1)[0], self.z3.eval(neg_inf_bv, 1)[0])

        # Test conversion of subnormal numbers
        subnormal_bv = self.fp_subnormal.to_bv()
        self.assertEqual(subnormal_bv.length, 32)


if __name__ == "__main__":
    unittest.main()
