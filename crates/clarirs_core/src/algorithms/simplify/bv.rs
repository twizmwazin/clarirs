use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use crate::{
    algorithms::simplify::{
        extract_bitvec_child, extract_bool_child, extract_float_child, extract_string_child,
    },
    ast::bitvec::BitVecOpExt,
    prelude::*,
};

pub(crate) fn simplify_bv<'c>(
    ast: &BitVecAst<'c>,
    children: &Vec<DynAst<'c>>,
) -> Result<BitVecAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match &ast.op() {
        BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => Ok(ast.clone()),
        BitVecOp::Not(..) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => ctx.bvv((!value.clone())?),
                _ => ctx.not(&arc),
            }
        }
        BitVecOp::And(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() & value2.clone())?)
                }
                _ => ctx.and(&arc, &arc1),
            }
        }
        BitVecOp::Or(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() | value2.clone())?)
                }
                _ => ctx.or(&arc, &arc1),
            }
        }
        BitVecOp::Xor(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() ^ value2.clone())?)
                }
                _ => ctx.xor(&arc, &arc1),
            }
        }
        BitVecOp::Neg(..) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => ctx.bvv((-value.clone())?),
                _ => ctx.neg(&arc),
            }
        }
        BitVecOp::Abs(..) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => {
                    // Check if the value is negative by examining the sign bit
                    if value.sign() {
                        // If negative, return the negated value
                        ctx.bvv((-value.clone())?)
                    } else {
                        // If positive, return the value as-is
                        ctx.bvv(value.clone())
                    }
                }
                _ => ctx.abs(&arc),
            }
        }
        BitVecOp::Add(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() + value2.clone())?)
                }
                _ => ctx.add(&arc, &arc1),
            }
        }
        BitVecOp::Sub(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() - value2.clone())?)
                }
                _ => ctx.sub(&arc, &arc1),
            }
        }
        BitVecOp::Mul(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() * value2.clone())?)
                }
                _ => ctx.mul(&arc, &arc1),
            }
        }
        BitVecOp::UDiv(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    ctx.bvv((value1.clone() / value2.clone())?)
                }
                _ => ctx.udiv(&arc, &arc1),
            }
        }
        BitVecOp::SDiv(..) => {
            let (dividend_ast, divisor_ast) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (dividend_ast.op(), divisor_ast.op()) {
                (BitVecOp::BVV(dividend_val), BitVecOp::BVV(divisor_val)) => {
                    ctx.bvv((dividend_val.sdiv(divisor_val))?)
                }
                _ => ctx.sdiv(&dividend_ast, &divisor_ast),
            }
        }
        BitVecOp::URem(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => ctx.bvv(value1.urem(value2)),
                _ => ctx.urem(&arc, &arc1),
            }
        }
        BitVecOp::SRem(..) => {
            let (dividend_ast, divisor_ast) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (dividend_ast.op(), divisor_ast.op()) {
                (BitVecOp::BVV(dividend_val), BitVecOp::BVV(divisor_val)) => {
                    ctx.bvv((dividend_val.srem(divisor_val))?)
                }
                _ => ctx.srem(&dividend_ast, &divisor_ast),
            }
        }
        BitVecOp::ShL(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                    let shift_amount_u32 = shift_amount.to_u64().unwrap_or(0) as u32;
                    let result = value.clone() << shift_amount_u32;
                    ctx.bvv(result?)
                }
                _ => ctx.shl(&arc, &arc1),
            }
        }
        BitVecOp::LShR(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                    let bit_width = value.len();
                    let shift_amount_u32 = shift_amount.to_u64().unwrap_or(0) as u32;

                    let result = if shift_amount_u32 >= bit_width {
                        BitVec::zeros(bit_width)
                    } else if shift_amount_u32 == 0 {
                        value.clone()
                    } else {
                        (value.clone() >> shift_amount_u32)?
                    };
                    ctx.bvv(result)
                }
                _ => ctx.lshr(&arc, &arc1),
            }
        }
        BitVecOp::AShR(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
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
                            ctx.bvv(BitVec::from_biguint_trunc(
                                &((BigUint::one() << bit_length) - BigUint::one()),
                                bit_length,
                            ))
                        } else {
                            ctx.bvv(BitVec::zeros(bit_length))
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

                    ctx.bvv(BitVec::from_biguint_trunc(&result, bit_length))
                }
                _ => ctx.ashr(&arc, &arc1),
            }
        }
        BitVecOp::RotateLeft(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value_bv), BitVecOp::BVV(rotate_bv)) => {
                    let rotate_u32 = rotate_bv.to_u64().unwrap_or(0) as u32;
                    let rotated_bv = value_bv.rotate_left(rotate_u32)?;
                    ctx.bvv(rotated_bv)
                }
                _ => ctx.rotate_left(&arc, &arc1),
            }
        }
        BitVecOp::RotateRight(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value_bv), BitVecOp::BVV(rotate_amount_bv)) => {
                    let rotate_u32 = rotate_amount_bv.to_u64().unwrap_or(0) as u32;
                    let rotated_bv = value_bv.rotate_right(rotate_u32)?;
                    ctx.bvv(rotated_bv)
                }
                _ => ctx.rotate_right(&arc, &arc1),
            }
        }
        BitVecOp::ZeroExt(_, num_bits) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => ctx.bvv(value.zero_extend(*num_bits)?),
                _ => ctx.zero_ext(&arc, *num_bits),
            }
        }
        BitVecOp::SignExt(_, num_bits) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => ctx.bvv(value.sign_extend(*num_bits)?),
                _ => ctx.sign_ext(&arc, *num_bits),
            }
        }
        BitVecOp::Extract(_, high, low) => {
            let arc = extract_bitvec_child!(children, 0);

            // If the extract bounds are the entire BV, return the inner value as-is
            if *high == arc.size() - 1 && *low == 0 {
                return Ok(arc);
            }

            match arc.op() {
                // Concrete BVV case
                BitVecOp::BVV(value) => ctx.bvv(value.extract(*low, *high)?),

                // Concat cases

                // Extracting the entire left side
                BitVecOp::Concat(lhs, rhs) if *high == arc.size() - 1 && *low == rhs.size() => {
                    Ok(lhs.clone())
                }
                // Extracting the entire right side
                BitVecOp::Concat(_, rhs) if *high == rhs.size() - 1 && *low == 0 => Ok(rhs.clone()),
                // Extracting a part of the left side
                BitVecOp::Concat(lhs, rhs) if *low >= rhs.size() => ctx
                    .extract(lhs, *high - rhs.size(), *low - rhs.size())?
                    .simplify(),
                // Extracting a part of the right side
                BitVecOp::Concat(_, rhs) if *high < rhs.size() => {
                    ctx.extract(rhs, *high, *low)?.simplify()
                }
                // Extracting a part that spans both sides
                BitVecOp::Concat(lhs, rhs) => {
                    // Extraction spans both left and right
                    // First extract the needed parts from each side
                    let left_part = ctx.extract(lhs, *high - rhs.size(), 0)?;
                    let right_part = ctx.extract(rhs, rhs.size() - 1, *low)?;

                    // Concatenate the extracted parts
                    // Simplify the result to apply further optimizations
                    ctx.concat(&left_part, &right_part)?.simplify()
                }
                _ => ctx.extract(&arc, *high, *low),
            }
        }
        BitVecOp::Concat(..) => {
            let (arc, arc1) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                    // Shift the first value to the left to make space, then OR with the second value
                    let concatenated_value =
                        ((value1.zero_extend(value2.len())? << value2.len())? | value2.clone())?;

                    // Return a new BitVec with the concatenated result and new length
                    ctx.bvv(concatenated_value)
                }
                _ => ctx.concat(&arc, &arc1),
            }
        }
        BitVecOp::Reverse(..) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => {
                    let reversed_bits = value.reverse_bytes()?;
                    ctx.bvv(reversed_bits)
                }
                _ => ctx.reverse(&arc),
            }
        }
        BitVecOp::FpToIEEEBV(..) => {
            let arc = extract_float_child!(children, 0);
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Convert the floating-point value to its IEEE 754 bit representation
                    let ieee_bits = float.to_ieee_bits();
                    let bit_length = float.fsort().size();

                    // Create a BitVec with the IEEE 754 representation
                    ctx.bvv(
                        BitVec::from_biguint(&ieee_bits, bit_length)
                            .expect("Failed to create BitVec from BigUint"),
                    )
                }
                _ => ctx.fp_to_ieeebv(&arc), // Fallback for non-concrete values
            }
        }
        BitVecOp::FpToUBV(_, bit_size, fprm) => {
            let arc = extract_float_child!(children, 0);
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Convert the float to an unsigned integer representation (BigUint)
                    let unsigned_value = float.to_unsigned_biguint().unwrap_or(BigUint::zero());

                    // Truncate or extend the result to fit within the specified bit size
                    let result_bitvec = BitVec::from_biguint_trunc(&unsigned_value, *bit_size);

                    ctx.bvv(result_bitvec)
                }
                _ => ctx.fp_to_ubv(&arc, *bit_size, fprm.clone()), // Fallback for non-concrete values
            }
        }
        BitVecOp::FpToSBV(_, bit_size, fprm) => {
            let arc = extract_float_child!(children, 0);
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Convert the float to a signed integer representation (BigInt)
                    let signed_value = float.to_signed_bigint().unwrap_or(BigInt::zero());

                    // Convert the signed value to BigUint for BitVec construction
                    let unsigned_value = signed_value.to_biguint().unwrap_or(BigUint::zero());

                    // Create a BitVec with the result, truncating or extending to fit within the specified bit size
                    let result_bitvec = BitVec::from_biguint_trunc(&unsigned_value, *bit_size);

                    ctx.bvv(result_bitvec)
                }
                _ => ctx.fp_to_sbv(&arc, *bit_size, fprm.clone()), // Fallback for non-concrete values
            }
        }
        BitVecOp::StrLen(..) => {
            let arc = extract_string_child!(children, 0);
            match arc.op() {
                StringOp::StringV(value) => {
                    // chars().count() returns the number of Unicode scalar values
                    let length = value.chars().count() as u64;
                    ctx.bvv(BitVec::from_prim_with_size(length, 64)?)
                }
                _ => ctx.strlen(&arc), // Fallback to symbolic
            }
        }
        BitVecOp::StrIndexOf(..) => {
            let (arc, arc1, arc2) = (
                extract_string_child!(children, 0),
                extract_string_child!(children, 1),
                extract_bitvec_child!(children, 2),
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

                    // Check if `t` exists in `s` starting from `i`
                    if i < s.len() {
                        match s[i..].find(t) {
                            Some(pos) => {
                                let result_index = (i + pos) as u64;
                                ctx.bvv(BitVec::from_prim_with_size(result_index, 64)?)
                            }
                            None => ctx.bvv(BitVec::from_prim_with_size(-1i64 as u64, 64)?), // -1 if not found
                        }
                    } else {
                        // If start index is out of bounds, return -1
                        ctx.bvv(BitVec::from_prim_with_size(-1i64 as u64, 64)?)
                    }
                }
                _ => ctx.strindexof(&arc, &arc1, &arc2), // Fallback to symbolic
            }
        }
        BitVecOp::StrToBV(..) => {
            let arc = extract_string_child!(children, 0);
            match arc.op() {
                StringOp::StringV(string) => {
                    if string.is_empty() {
                        let max_int = BigUint::from_str_radix("ffffffffffffffff", 16).unwrap();
                        return ctx.bvv(BitVec::from_biguint_trunc(&max_int, 64));
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
                        return ctx.bvv(BitVec::zeros(64));
                    }

                    ctx.bvv(BitVec::from_biguint_trunc(&value, 64))
                }
                _ => ctx.strtobv(&arc),
            }
        }
        BitVecOp::If(..) => {
            let (if_, then_, else_) = (
                extract_bool_child!(children, 0),
                extract_bitvec_child!(children, 1),
                extract_bitvec_child!(children, 2),
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
                BooleanOp::Not(inner) => ctx.if_(inner, &else_, &then_),
                _ => ctx.if_(&if_, &then_, &else_),
            }
        }
        BitVecOp::Annotated(_, annotation) => {
            let arc = extract_bitvec_child!(children, 0);
            if annotation.eliminatable() {
                Ok(arc)
            } else if annotation.relocatable() {
                ctx.annotated(&arc, annotation.clone())
            } else {
                Ok(ast.clone())
            }
        }
        BitVecOp::Union(..) => {
            let (lhs, rhs) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            ctx.union(&lhs, &rhs)
        }
        BitVecOp::Intersection(..) => {
            let (lhs, rhs) = (
                extract_bitvec_child!(children, 0),
                extract_bitvec_child!(children, 1),
            );
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            ctx.intersection(&lhs, &rhs)
        }
    }
}
