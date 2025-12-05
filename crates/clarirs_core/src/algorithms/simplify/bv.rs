use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use crate::{algorithms::simplify::SimplifyError, ast::bitvec::BitVecOpExt, prelude::*};

pub(crate) fn simplify_bv<'c>(
    state: &mut super::SimplifyState<'c>,
) -> Result<BitVecAst<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let bv_expr = state.expr.clone().into_bitvec().unwrap();

    match bv_expr.op() {
        BitVecOp::BVS(..) | BitVecOp::BVV(..) => Ok(bv_expr),
        BitVecOp::Not(..) => {
            let arc = state.get_bv_simplified(0)?;
            match arc.op() {
                BitVecOp::BVV(value) => Ok(ctx.bvv((!value.clone())?)?),
                _ => Ok(ctx.not(arc)?),
            }
        }
        BitVecOp::And(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() & value2.clone())?)?)
                }
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(ctx.bvv(v.clone())?),
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(ctx.bvv(v.clone())?),
                (BitVecOp::BVV(v), _) if v.is_all_ones() => Ok(arc1.clone()),
                (_, BitVecOp::BVV(v)) if v.is_all_ones() => Ok(arc.clone()),

                // Distribute AND over CONCAT when one operand is constant
                // (const & concat(a, b)) = concat(const_high & a, const_low & b)
                (BitVecOp::BVV(const_val), BitVecOp::Concat(concat_lhs, concat_rhs))
                | (BitVecOp::Concat(concat_lhs, concat_rhs), BitVecOp::BVV(const_val)) => {
                    let rhs_size = concat_rhs.size();
                    let lhs_size = concat_lhs.size();

                    // Extract the high and low parts of the constant
                    let const_high = const_val.extract(rhs_size, lhs_size + rhs_size - 1)?;
                    let const_low = const_val.extract(0, rhs_size - 1)?;

                    // AND each part with the corresponding concat operand
                    let high_and = ctx.and(&ctx.bvv(const_high)?, concat_lhs)?;
                    let low_and = ctx.and(&ctx.bvv(const_low)?, concat_rhs)?;

                    // Concatenate the results and recursively simplify
                    state.rerun(ctx.concat(&high_and, &low_and)?)
                }

                // Distribute AND over zero-extend when one operand is constant
                // (bvand ((_ zero_extend 56) BV8_instrumented_load_36) (_ bv255 64))
                //   -> ((_ zero_extend 56) (bvand BV8_instrumented_load_36 (_ bv255 8)))
                (BitVecOp::BVV(const_val), BitVecOp::ZeroExt(inner, ext_size))
                | (BitVecOp::ZeroExt(inner, ext_size), BitVecOp::BVV(const_val)) => {
                    let inner_size = inner.size();
                    let const_inner = const_val.extract(0, inner_size - 1)?;

                    let inner_and = ctx.and(&ctx.bvv(const_inner)?, inner)?;
                    let zero_extended = ctx.zero_ext(&inner_and, *ext_size)?;

                    state.rerun(zero_extended)
                }

                // x & ¬x = 0
                (BitVecOp::Not(lhs), rhs) if lhs.op() == rhs => {
                    Ok(ctx.bvv(BitVec::zeros(arc.size()))?)
                }
                (lhs, BitVecOp::Not(rhs)) if lhs == rhs.op() => {
                    Ok(ctx.bvv(BitVec::zeros(arc.size()))?)
                }
                _ => Ok(ctx.and(arc, arc1)?),
            }
        }
        BitVecOp::Or(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() | value2.clone())?)?)
                }
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc1.clone()),
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                (BitVecOp::BVV(v), _) if v.is_all_ones() => Ok(ctx.bvv(v.clone())?),
                (_, BitVecOp::BVV(v)) if v.is_all_ones() => Ok(ctx.bvv(v.clone())?),

                // Distribute OR over CONCAT when one operand is constant
                // (const | concat(a, b)) = concat(const_high | a, const_low | b)
                (BitVecOp::BVV(const_val), BitVecOp::Concat(concat_lhs, concat_rhs))
                | (BitVecOp::Concat(concat_lhs, concat_rhs), BitVecOp::BVV(const_val)) => {
                    let rhs_size = concat_rhs.size();
                    let lhs_size = concat_lhs.size();

                    // Extract the high and low parts of the constant
                    let const_high = const_val.extract(rhs_size, lhs_size + rhs_size - 1)?;
                    let const_low = const_val.extract(0, rhs_size - 1)?;

                    // OR each part with the corresponding concat operand
                    let high_or = ctx.or(&ctx.bvv(const_high)?, concat_lhs)?;
                    let low_or = ctx.or(&ctx.bvv(const_low)?, concat_rhs)?;

                    // Concatenate the results and recursively simplify
                    state.rerun(ctx.concat(&high_or, &low_or)?)
                }

                // x | ¬x = -1 (all ones)
                (BitVecOp::Not(lhs), rhs) if lhs.op() == rhs => {
                    Ok(ctx.bvv(BitVec::from_biguint_trunc(
                        &((BigUint::one() << arc.size()) - BigUint::one()),
                        arc.size(),
                    ))?)
                }
                (lhs, BitVecOp::Not(rhs)) if lhs == rhs.op() => {
                    Ok(ctx.bvv(BitVec::from_biguint_trunc(
                        &((BigUint::one() << arc.size()) - BigUint::one()),
                        arc.size(),
                    ))?)
                }
                _ => Ok(ctx.or(arc, arc1)?),
            }
        }
        BitVecOp::Xor(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() ^ value2.clone())?)?)
                }
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc1.clone()),
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                (BitVecOp::BVV(v), _) if v.is_all_ones() => Ok(ctx.not(arc1)?),
                (_, BitVecOp::BVV(v)) if v.is_all_ones() => Ok(ctx.not(arc)?),

                // ¬a ^ ¬b = a ^ b
                (BitVecOp::Not(lhs), BitVecOp::Not(rhs)) => state.rerun(ctx.xor(lhs, rhs)?),

                // Distribute XOR over CONCAT when one operand is constant
                // (const ^ concat(a, b)) = concat(const_high ^ a, const_low ^ b)
                (BitVecOp::BVV(const_val), BitVecOp::Concat(concat_lhs, concat_rhs))
                | (BitVecOp::Concat(concat_lhs, concat_rhs), BitVecOp::BVV(const_val)) => {
                    let rhs_size = concat_rhs.size();
                    let lhs_size = concat_lhs.size();

                    // Extract the high and low parts of the constant
                    let const_high = const_val.extract(rhs_size, lhs_size + rhs_size - 1)?;
                    let const_low = const_val.extract(0, rhs_size - 1)?;

                    // XOR each part with the corresponding concat operand
                    let high_xor = ctx.xor(&ctx.bvv(const_high)?, concat_lhs)?;
                    let low_xor = ctx.xor(&ctx.bvv(const_low)?, concat_rhs)?;

                    // Concatenate the results and recursively simplify
                    state.rerun(ctx.concat(&high_xor, &low_xor)?)
                }

                _ => Ok(ctx.xor(arc, arc1)?),
            }
        }
        BitVecOp::Neg(..) => {
            let arc = state.get_bv_simplified(0)?;
            match arc.op() {
                BitVecOp::BVV(value) => Ok(ctx.bvv((-value.clone())?)?),
                // -(-x) = x (double negation)
                BitVecOp::Neg(inner) => Ok(inner.clone()),
                _ => Ok(ctx.neg(arc)?),
            }
        }
        BitVecOp::Add(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() + value2.clone())?)?)
                }
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc1.clone()),
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                _ => Ok(ctx.add(arc, arc1)?),
            }
        }
        BitVecOp::Sub(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() - value2.clone())?)?)
                }
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                (lhs_op, rhs_op) if lhs_op == rhs_op => Ok(ctx.bvv(BitVec::zeros(arc.size()))?),
                _ => Ok(ctx.sub(arc, arc1)?),
            }
        }
        BitVecOp::Mul(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() * value2.clone())?)?)
                }
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(ctx.bvv(v.clone())?),
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(ctx.bvv(v.clone())?),
                (BitVecOp::BVV(v), _) if v.to_u64() == Some(1) => Ok(arc1.clone()),
                (_, BitVecOp::BVV(v)) if v.to_u64() == Some(1) => Ok(arc.clone()),
                _ => Ok(ctx.mul(arc, arc1)?),
            }
        }
        BitVecOp::UDiv(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() / value2.clone())?)?)
                }
                (_, BitVecOp::BVV(v)) if v.to_u64() == Some(1) => Ok(arc.clone()),
                _ => Ok(ctx.udiv(arc, arc1)?),
            }
        }
        BitVecOp::SDiv(..) => {
            let (dividend_ast, divisor_ast) =
                (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (dividend_ast.op(), divisor_ast.op()) {
                (BitVecOp::BVV(dividend_val), BitVecOp::BVV(divisor_val)) => {
                    Ok(ctx.bvv((dividend_val.sdiv(divisor_val))?)?)
                }
                (_, BitVecOp::BVV(v)) if v.to_u64() == Some(1) => Ok(dividend_ast.clone()),
                _ => Ok(ctx.sdiv(dividend_ast, divisor_ast)?),
            }
        }
        BitVecOp::URem(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => Ok(ctx.bvv(value1.urem(value2))?),
                _ => Ok(ctx.urem(arc, arc1)?),
            }
        }
        BitVecOp::SRem(..) => {
            let (dividend_ast, divisor_ast) =
                (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (dividend_ast.op(), divisor_ast.op()) {
                (BitVecOp::BVV(dividend_val), BitVecOp::BVV(divisor_val)) => {
                    Ok(ctx.bvv((dividend_val.srem(divisor_val))?)?)
                }
                _ => Ok(ctx.srem(dividend_ast, divisor_ast)?),
            }
        }
        BitVecOp::ShL(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                // Fully concrete case
                (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                    let bit_width = value.len();
                    let shift_amount_u32 = shift_amount.to_u64().unwrap_or(0) as u32;

                    // If shifting >= bit_width, result is 0
                    if shift_amount_u32 >= bit_width {
                        Ok(ctx.bvv(BitVec::zeros(bit_width))?)
                    } else if shift_amount_u32 == 0 {
                        Ok(arc.clone())
                    } else {
                        let result = (value.clone() << shift_amount_u32)?;
                        Ok(ctx.bvv(result)?)
                    }
                }
                // Fallback case
                _ => Ok(ctx.shl(arc, arc1)?),
            }
        }
        BitVecOp::LShR(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                // Fully concrete case
                (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                    let bit_width = value.len();
                    let shift_amount_u32 = shift_amount.to_u64().unwrap_or(0) as u32;
                    if shift_amount_u32 >= bit_width {
                        Ok(ctx.bvv(BitVec::zeros(bit_width))?)
                    } else if shift_amount_u32 == 0 {
                        Ok(arc.clone())
                    } else {
                        let result = value.clone() >> shift_amount_u32;
                        Ok(ctx.bvv(result?)?)
                    }
                }
                // Fallback case
                _ => Ok(ctx.lshr(arc, arc1)?),
            }
        }
        BitVecOp::AShR(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Zero shift amount
                (_, BitVecOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                // Fully concrete case
                (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                    let shift_amount_u32 = shift_amount.to_u64().unwrap_or(0) as u32;
                    let bit_length = value.len();

                    // Convert value to BigUint
                    let unsigned_value = value.to_biguint();

                    // Check sign bit
                    let sign_bit_set = (unsigned_value.clone() >> (bit_length - 1))
                        & BigUint::one()
                        != BigUint::zero();

                    // If shifting >= bit_length, return all-ones (if negative) or all-zeros (if positive)
                    if shift_amount_u32 >= bit_length {
                        return if sign_bit_set {
                            Ok(ctx.bvv(BitVec::from_biguint_trunc(
                                &((BigUint::one() << bit_length) - BigUint::one()),
                                bit_length,
                            ))?)
                        } else {
                            Ok(ctx.bvv(BitVec::zeros(bit_length))?)
                        };
                    }

                    // Perform the shift
                    let unsigned_shifted = unsigned_value.clone() >> shift_amount_u32;

                    // Extend the sign bit if needed
                    let result = if sign_bit_set {
                        // Create a mask to extend the sign bit
                        let mask = ((BigUint::one() << shift_amount_u32) - BigUint::one())
                            << (bit_length - shift_amount_u32);
                        unsigned_shifted | mask
                    } else {
                        unsigned_shifted
                    };

                    Ok(ctx.bvv(BitVec::from_biguint_trunc(&result, bit_length))?)
                }
                // Fallback case
                _ => Ok(ctx.ashr(arc, arc1)?),
            }
        }
        BitVecOp::RotateLeft(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero or multiple of size
                (_, BitVecOp::BVV(v))
                    if v.is_zero() || v.to_bigint() % arc.size() == BigInt::zero() =>
                {
                    Ok(arc.clone())
                }
                // Fully concrete case
                (BitVecOp::BVV(value_bv), BitVecOp::BVV(rotate_bv)) => {
                    let rotate_u32 = rotate_bv.to_u64().unwrap_or(0) as u32;
                    let rotated_bv = value_bv.rotate_left(rotate_u32)?;
                    Ok(ctx.bvv(rotated_bv)?)
                }
                // Nested rotation with concrete amounts - combine them
                // rotate_left(rotate_left(x, c1), c2) => rotate_left(x, (c1 + c2) % size)
                (BitVecOp::RotateLeft(inner, inner_amt), BitVecOp::BVV(outer_amt)) => {
                    if let BitVecOp::BVV(inner_amt_val) = inner_amt.op() {
                        let size = arc.size();
                        let combined_amt = (inner_amt_val.to_bigint() + outer_amt.to_bigint())
                            % BigInt::from(size);
                        let combined_amt_bv = BitVec::from_bigint(&combined_amt, arc1.size())?;
                        Ok(ctx
                            .rotate_left(inner.clone(), ctx.bvv(combined_amt_bv)?)?
                            .simplify()?)
                    } else {
                        // Inner rotation amount is not concrete, fall through
                        let rotate_amount_u32 = outer_amt.to_u64().unwrap_or(0) as u32;
                        let bottom = ctx.extract(&arc, rotate_amount_u32 - 1, 0)?;
                        let top = ctx.extract(&arc, arc.size() - 1, rotate_amount_u32)?;
                        Ok(ctx.concat(bottom, top)?.simplify()?)
                    }
                }
                // Fallback case
                _ => Ok(ctx.rotate_left(arc, arc1)?),
            }
        }
        BitVecOp::RotateRight(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (BitVecOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero or multiple of size
                (_, BitVecOp::BVV(v))
                    if v.is_zero() || v.to_bigint() % arc.size() == BigInt::zero() =>
                {
                    Ok(arc.clone())
                }
                // Fully concrete case
                (BitVecOp::BVV(value_bv), BitVecOp::BVV(rotate_amount_bv)) => {
                    let rotate_u32 = rotate_amount_bv.to_u64().unwrap_or(0) as u32;
                    let rotated_bv = value_bv.rotate_right(rotate_u32)?;
                    Ok(ctx.bvv(rotated_bv)?)
                }
                // Nested rotation with concrete amounts - combine them
                // rotate_right(rotate_right(x, c1), c2) => rotate_right(x, (c1 + c2) % size)
                (BitVecOp::RotateRight(inner, inner_amt), BitVecOp::BVV(outer_amt)) => {
                    if let BitVecOp::BVV(inner_amt_val) = inner_amt.op() {
                        let size = arc.size();
                        let combined_amt = (inner_amt_val.to_bigint() + outer_amt.to_bigint())
                            % BigInt::from(size);
                        let combined_amt_bv = BitVec::from_bigint(&combined_amt, arc1.size())?;
                        Ok(ctx
                            .rotate_right(inner.clone(), ctx.bvv(combined_amt_bv)?)?
                            .simplify()?)
                    } else {
                        // Inner rotation amount is not concrete, fall through
                        let rotate_amount_u32 = outer_amt.to_u64().unwrap_or(0) as u32;
                        let bottom = ctx.extract(&arc, arc.size() - rotate_amount_u32, 0)?;
                        let top =
                            ctx.extract(&arc, arc.size() - 1, arc.size() - rotate_amount_u32)?;
                        Ok(ctx.concat(top, bottom)?.simplify()?)
                    }
                }
                // Fallback case
                _ => Ok(ctx.rotate_right(arc, arc1)?),
            }
        }
        BitVecOp::ZeroExt(_, num_bits) => {
            let arc = state.get_bv_simplified(0)?;
            match (arc.op(), num_bits) {
                // Zero extension
                (_, 0) => Ok(arc.clone()),
                // Concrete BVV case
                (BitVecOp::BVV(value), _) => Ok(ctx.bvv(value.zero_extend(*num_bits)?)?),
                // Nested ZeroExt - combine extensions
                (BitVecOp::ZeroExt(inner, inner_num_bits), _) => {
                    let total_ext = inner_num_bits + num_bits;
                    Ok(ctx.zero_ext(inner, total_ext)?)
                }
                // Symbolic case
                (_, _) => Ok(ctx.zero_ext(arc, *num_bits)?),
            }
        }
        BitVecOp::SignExt(_, num_bits) => {
            let arc = state.get_bv_simplified(0)?;
            match (arc.op(), num_bits) {
                // Sign extension
                (_, 0) => Ok(arc.clone()),
                // Concrete BVV case
                (BitVecOp::BVV(value), _) => Ok(ctx.bvv(value.sign_extend(*num_bits)?)?),
                // Nested SignExt - combine extensions
                (BitVecOp::SignExt(inner, inner_num_bits), _) => {
                    let total_ext = inner_num_bits + num_bits;
                    Ok(ctx.sign_ext(inner, total_ext)?)
                }
                // Fallback case
                (_, _) => Ok(ctx.sign_ext(arc, *num_bits)?),
            }
        }
        BitVecOp::Extract(_, high, low) => {
            let arc = state.get_bv_simplified(0)?;

            // If the extract bounds are the entire BV, return the inner value as-is
            if *high == arc.size() - 1 && *low == 0 {
                return Ok(arc);
            }

            match arc.op() {
                // Concrete BVV case
                BitVecOp::BVV(value) => Ok(ctx.bvv(value.extract(*low, *high)?)?),

                // Propagate extract through bitwise operations
                // extract(n, m, a & b) = extract(n, m, a) & extract(n, m, b)
                BitVecOp::And(lhs, rhs) => {
                    let lhs_extracted = ctx.extract(lhs, *high, *low)?;
                    let rhs_extracted = ctx.extract(rhs, *high, *low)?;
                    state.rerun(ctx.and(&lhs_extracted, &rhs_extracted)?)
                }
                // extract(n, m, a | b) = extract(n, m, a) | extract(n, m, b)
                BitVecOp::Or(lhs, rhs) => {
                    let lhs_extracted = ctx.extract(lhs, *high, *low)?;
                    let rhs_extracted = ctx.extract(rhs, *high, *low)?;
                    state.rerun(ctx.or(&lhs_extracted, &rhs_extracted)?)
                }
                // extract(n, m, a ^ b) = extract(n, m, a) ^ extract(n, m, b)
                BitVecOp::Xor(lhs, rhs) => {
                    let lhs_extracted = ctx.extract(lhs, *high, *low)?;
                    let rhs_extracted = ctx.extract(rhs, *high, *low)?;
                    state.rerun(ctx.xor(&lhs_extracted, &rhs_extracted)?)
                }
                // extract(n, m, ~a) = ~extract(n, m, a)
                BitVecOp::Not(inner) => {
                    let inner_extracted = ctx.extract(inner, *high, *low)?;
                    state.rerun(ctx.not(&inner_extracted)?)
                }

                // ZeroExt cases
                // If extracting from the original bits (not the extended zero bits)
                BitVecOp::ZeroExt(inner, _) if *high < inner.size() => {
                    Ok(ctx.extract(inner, *high, *low)?.simplify()?)
                }
                // If extracting only from the extended zero bits
                BitVecOp::ZeroExt(inner, _) if *low >= inner.size() => {
                    Ok(ctx.bvv(BitVec::zeros(*high - *low + 1))?)
                }

                // SignExt cases
                // If extracting from the original bits (not the extended sign bits)
                BitVecOp::SignExt(inner, _) if *high < inner.size() => {
                    Ok(ctx.extract(inner, *high, *low)?.simplify()?)
                }
                // If extracting only from the extended sign bits
                BitVecOp::SignExt(inner, _) if *low >= inner.size() => {
                    let sign_bit = ctx.extract(inner, inner.size() - 1, inner.size() - 1)?;
                    // Replicate the sign bit for the extracted width
                    let width = *high - *low + 1;
                    let mut result = sign_bit.clone();
                    for _ in 1..width {
                        result = ctx.concat(&sign_bit, result)?;
                    }
                    Ok(result)
                }

                // Concat cases
                // Extracting the entire left side
                BitVecOp::Concat(lhs, rhs) if *high == arc.size() - 1 && *low == rhs.size() => {
                    Ok(lhs.clone())
                }
                // Extracting the entire right side
                BitVecOp::Concat(_, rhs) if *high == rhs.size() - 1 && *low == 0 => Ok(rhs.clone()),
                // Extracting a part of the left side
                BitVecOp::Concat(lhs, rhs) if *low >= rhs.size() => Ok(ctx
                    .extract(lhs, *high - rhs.size(), *low - rhs.size())?
                    .simplify()?),
                // Extracting a part of the right side
                BitVecOp::Concat(_, rhs) if *high < rhs.size() => {
                    Ok(ctx.extract(rhs, *high, *low)?.simplify()?)
                }
                // Extracting a part that spans both sides
                BitVecOp::Concat(lhs, rhs) => {
                    // Extraction spans both left and right
                    // First extract the needed parts from each side
                    let left_part = ctx.extract(lhs, *high - rhs.size(), 0)?;
                    let right_part = ctx.extract(rhs, rhs.size() - 1, *low)?;

                    // Concatenate the extracted parts
                    // Simplify the result to apply further optimizations
                    Ok(ctx.concat(left_part, right_part)?.simplify()?)
                }
                _ => Ok(ctx.extract(arc, *high, *low)?),
            }
        }
        BitVecOp::Concat(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    let concatenated_value = value1.concat(value2)?;

                    // Return a new BitVec with the concatenated result and new length
                    Ok(ctx.bvv(concatenated_value)?)
                }
                // Match cases where one side's size is zero
                (lhs, _) if lhs.size() == 0 => Ok(arc1.clone()),
                (_, rhs) if rhs.size() == 0 => Ok(arc.clone()),

                _ => Ok(ctx.concat(arc, arc1)?),
            }
        }
        BitVecOp::ByteReverse(..) => {
            let arc = state.get_bv_simplified(0)?;
            match arc.op() {
                BitVecOp::BVV(value) => {
                    let reversed_bits = value.reverse_bytes()?;
                    Ok(ctx.bvv(reversed_bits)?)
                }
                _ => Ok(ctx.byte_reverse(arc)?),
            }
        }
        BitVecOp::FpToIEEEBV(..) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Convert the floating-point value to its IEEE 754 bit representation
                    let ieee_bits = float.to_ieee_bits();
                    let bit_length = float.fsort().size();

                    // Create a BitVec with the IEEE 754 representation
                    Ok(ctx.bvv(
                        BitVec::from_biguint(&ieee_bits, bit_length)
                            .expect("Failed to create BitVec from BigUint"),
                    )?)
                }
                _ => Ok(ctx.fp_to_ieeebv(arc)?), // Fallback for non-concrete values
            }
        }
        BitVecOp::FpToUBV(_, bit_size, fprm) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Convert the float to an unsigned integer representation (BigUint)
                    let unsigned_value = float.to_unsigned_biguint().unwrap_or(BigUint::zero());

                    // Truncate or extend the result to fit within the specified bit size
                    let result_bitvec = BitVec::from_biguint_trunc(&unsigned_value, *bit_size);

                    Ok(ctx.bvv(result_bitvec)?)
                }
                _ => Ok(ctx.fp_to_ubv(arc, *bit_size, *fprm)?), // Fallback for non-concrete values
            }
        }
        BitVecOp::FpToSBV(_, bit_size, fprm) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Convert the float to a signed integer representation (BigInt)
                    let signed_value = float.to_signed_bigint().unwrap_or(BigInt::zero());

                    // Convert the signed value to BigUint for BitVec construction
                    let unsigned_value = signed_value.to_biguint().unwrap_or(BigUint::zero());

                    // Create a BitVec with the result, truncating or extending to fit within the specified bit size
                    let result_bitvec = BitVec::from_biguint_trunc(&unsigned_value, *bit_size);

                    Ok(ctx.bvv(result_bitvec)?)
                }
                _ => Ok(ctx.fp_to_sbv(arc, *bit_size, *fprm)?), // Fallback for non-concrete values
            }
        }
        BitVecOp::StrLen(..) => {
            let arc = state.get_string_simplified(0)?;
            match arc.op() {
                StringOp::StringV(value) => {
                    // chars().count() returns the number of Unicode scalar values
                    let length = value.chars().count() as u64;
                    Ok(ctx.bvv(BitVec::from_prim_with_size(length, 64)?)?)
                }
                _ => Ok(ctx.strlen(arc)?), // Fallback to symbolic
            }
        }
        BitVecOp::StrIndexOf(..) => {
            let (arc, arc1, arc2) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
                state.get_bv_simplified(2)?,
            );

            match (arc.op(), arc1.op(), arc2.op()) {
                (
                    StringOp::StringV(input_string),
                    StringOp::StringV(substring),
                    BitVecOp::BVV(start_index),
                ) => {
                    let s = input_string;
                    let t = substring;
                    let i = start_index.to_usize().unwrap_or(0);

                    // Use character count for Unicode-aware indexing
                    let char_count = s.chars().count();

                    // Check if `t` exists in `s` starting from character index `i`
                    if i < char_count {
                        // Convert character index to byte index
                        let byte_index = s
                            .char_indices()
                            .nth(i)
                            .map(|(idx, _)| idx)
                            .unwrap_or(s.len());

                        match s[byte_index..].find(t) {
                            Some(pos) => {
                                // Convert byte position back to character position
                                let byte_pos = byte_index + pos;
                                let char_pos = s[..byte_pos].chars().count();
                                Ok(ctx.bvv(BitVec::from_prim_with_size(char_pos as u64, 64)?)?)
                            }
                            None => Ok(ctx.bvv(BitVec::from_prim_with_size(-1i64 as u64, 64)?)?), // -1 if not found
                        }
                    } else {
                        // If start index is out of bounds, return -1
                        Ok(ctx.bvv(BitVec::from_prim_with_size(-1i64 as u64, 64)?)?)
                    }
                }
                _ => Ok(ctx.strindexof(arc, arc1, arc2)?), // Fallback to symbolic
            }
        }
        BitVecOp::StrToBV(..) => {
            let arc = state.get_string_simplified(0)?;
            match arc.op() {
                StringOp::StringV(string) => {
                    if string.is_empty() {
                        let max_int = BigUint::from_str_radix("ffffffffffffffff", 16).unwrap();
                        return Ok(ctx.bvv(BitVec::from_biguint_trunc(&max_int, 64))?);
                    }

                    // Attempt to parse the string as a decimal integer
                    let value = BigUint::from_str_radix(string, 10)
                        .or_else(|_| BigUint::from_str_radix(string, 16)) // Try hexadecimal if decimal fails
                        .or_else(|_| BigUint::from_str_radix(string, 2)) // Try binary if hexadecimal fails
                        .unwrap_or_else(|_| {
                            BigUint::from_str_radix("ffffffffffffffff", 16).unwrap()
                        });

                    // If the parsed number is too large to fit in 64 bits, return 0.
                    if value >= BigUint::from(2u64).pow(64) {
                        return Ok(ctx.bvv(BitVec::zeros(64))?);
                    }

                    Ok(ctx.bvv(BitVec::from_biguint_trunc(&value, 64))?)
                }
                _ => Ok(ctx.strtobv(arc)?),
            }
        }
        BitVecOp::If(..) => {
            let (if_, then_, else_) = (
                state.get_bool_simplified(0)?,
                state.get_bv_simplified(1)?,
                state.get_bv_simplified(2)?,
            );

            // If both branches are identical, return either one
            if then_ == else_ {
                return Ok(then_.clone());
            }

            match if_.op() {
                // If the condition is a concrete boolean value, return the appropriate branch
                BooleanOp::BoolV(value) => {
                    if *value {
                        Ok(then_.clone())
                    } else {
                        Ok(else_.clone())
                    }
                }
                // If the condition has a Not at the top level, invert the branches
                BooleanOp::Not(inner) => state.rerun(ctx.if_(inner, else_, then_)?),
                _ => Ok(ctx.if_(if_, then_, else_)?),
            }
        }
        BitVecOp::Union(..) => {
            let (lhs, rhs) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            Ok(ctx.union(lhs, rhs)?)
        }
        BitVecOp::Intersection(..) => {
            let (lhs, rhs) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            Ok(ctx.intersection(lhs, rhs)?)
        }
    }
}
