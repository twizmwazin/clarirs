use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use crate::{algorithms::simplify::simplify, ast::bitvec::BitVecExt, prelude::*};

#[allow(unused_variables)]
impl<'c> Simplify<'c> for BitVecAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        let hash = self.hash();

        ctx.simplification_cache.get_or_insert_with_bv(hash, || {
            match &self.op() {
                BitVecOp::BVS(name, width) => ctx.bvs(name.clone(), *width),
                BitVecOp::BVV(_) => Ok(self.clone()),
                BitVecOp::Not(ast) => {
                    simplify!(ast);
                    match ast.op() {
                        BitVecOp::BVV(value) => ctx.bvv((!value.clone())?),
                        _ => ctx.not(&ast),
                    }
                }
                BitVecOp::And(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv((value1.clone() & value2.clone())?)
                        }
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BitVecOp::Or(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv((value1.clone() | value2.clone())?)
                        }
                        _ => ctx.or(&arc, &arc1),
                    }
                }
                BitVecOp::Xor(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv((value1.clone() ^ value2.clone())?)
                        }
                        _ => ctx.xor(&arc, &arc1),
                    }
                }
                BitVecOp::Abs(arc) => {
                    simplify!(arc);
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
                BitVecOp::Add(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv((value1.clone() + value2.clone())?)
                        }
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BitVecOp::Sub(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv((value1.clone() - value2.clone())?)
                        }
                        _ => ctx.sub(&arc, &arc1),
                    }
                }
                BitVecOp::Mul(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv((value1.clone() * value2.clone())?)
                        }
                        _ => ctx.mul(&arc, &arc1),
                    }
                }
                BitVecOp::UDiv(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            let quotient = BitVec::from_biguint_trunc(
                                &(value1.to_biguint() / value2.to_biguint()),
                                value1.len(),
                            );
                            ctx.bvv(quotient)
                        }
                        _ => ctx.udiv(&arc, &arc1),
                    }
                }
                BitVecOp::SDiv(dividend_ast, divisor_ast) => {
                    simplify!(dividend_ast, divisor_ast);

                    match (dividend_ast.op(), divisor_ast.op()) {
                        (BitVecOp::BVV(dividend_val), BitVecOp::BVV(divisor_val)) => {
                            ctx.bvv((dividend_val.sdiv(divisor_val))?)
                        }
                        _ => ctx.sdiv(&dividend_ast, &divisor_ast),
                    }
                }

                BitVecOp::URem(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.urem(value2))
                        }
                        _ => ctx.urem(&arc, &arc1),
                    }
                }
                BitVecOp::SRem(dividend_ast, divisor_ast) => {
                    simplify!(dividend_ast, divisor_ast);

                    match (dividend_ast.op(), divisor_ast.op()) {
                        (BitVecOp::BVV(dividend_val), BitVecOp::BVV(divisor_val)) => {
                            ctx.bvv((dividend_val.srem(divisor_val))?)
                        }
                        _ => ctx.srem(&dividend_ast, &divisor_ast),
                    }
                }

                BitVecOp::Pow(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(base), BitVecOp::BVV(exp)) => ctx.bvv(base.pow(exp)?),
                        _ => ctx.pow(&arc, &arc1),
                    }
                }

                BitVecOp::ShL(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                            let shift_amount_usize = shift_amount.to_usize().unwrap_or(0);
                            let result = value.clone() << shift_amount_usize;
                            ctx.bvv(result?)
                        }
                        _ => ctx.shl(&arc, &arc1),
                    }
                }
                BitVecOp::LShR(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                            let bit_width = value.len();
                            let shift_amount_usize = shift_amount.to_usize().unwrap_or(0);

                            let result = if shift_amount_usize >= bit_width {
                                BitVec::zeros(bit_width)
                            } else if shift_amount_usize == 0 {
                                value.clone()
                            } else {
                                (value.clone() >> shift_amount_usize)?
                            };
                            ctx.bvv(result)
                        }
                        _ => ctx.lshr(&arc, &arc1),
                    }
                }

                BitVecOp::AShR(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                            let shift_amount_usize = shift_amount.to_usize().unwrap_or(0);
                            let bit_length = value.len();

                            // Convert value to BigUint
                            let unsigned_value = value.to_biguint();

                            // Check sign bit
                            let sign_bit_set = (unsigned_value.clone() >> (bit_length - 1))
                                & BigUint::one()
                                != BigUint::zero();

                            // If shifting >= bit_length, return all-ones (if negative) or all-zeros (if positive)
                            if shift_amount_usize >= bit_length {
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
                            let unsigned_shifted = unsigned_value.clone() >> shift_amount_usize;

                            // Extend the sign bit if needed
                            let result = if sign_bit_set {
                                // Create a mask to extend the sign bit
                                let mask = ((BigUint::one() << shift_amount_usize)
                                    - BigUint::one())
                                    << (bit_length - shift_amount_usize);
                                unsigned_shifted | mask
                            } else {
                                unsigned_shifted
                            };

                            ctx.bvv(BitVec::from_biguint_trunc(&result, bit_length))
                        }
                        _ => ctx.ashr(&arc, &arc1),
                    }
                }
                BitVecOp::RotateLeft(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value_bv), BitVecOp::BVV(rotate_bv)) => {
                            let rotate_usize = rotate_bv.to_usize().unwrap_or(0);
                            let rotated_bv = value_bv.rotate_left(rotate_usize)?;
                            ctx.bvv(rotated_bv)
                        }
                        _ => ctx.rotate_left(&arc, &arc1),
                    }
                }
                BitVecOp::RotateRight(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value_bv), BitVecOp::BVV(rotate_amount_bv)) => {
                            let rotate_usize = rotate_amount_bv.to_usize().unwrap_or(0);
                            let rotated_bv = value_bv.rotate_right(rotate_usize)?;
                            ctx.bvv(rotated_bv)
                        }
                        _ => ctx.rotate_right(&arc, &arc1),
                    }
                }
                BitVecOp::ZeroExt(arc, num_bits) => {
                    simplify!(arc);

                    match arc.op() {
                        BitVecOp::BVV(value) => ctx.bvv(value.zero_extend(*num_bits as usize)?),
                        _ => ctx.zero_ext(&arc, *num_bits),
                    }
                }
                BitVecOp::SignExt(arc, num_bits) => {
                    simplify!(arc);
                    match arc.op() {
                        BitVecOp::BVV(value) => ctx.bvv(value.sign_extend(*num_bits as usize)?),
                        _ => ctx.sign_ext(&arc, *num_bits),
                    }
                }
                BitVecOp::Extract(arc, high, low) => {
                    simplify!(arc);

                    // If the extract bounds are the entire BV, return the inner value as-is
                    if *high == arc.size() - 1 && *low == 0 {
                        return Ok(arc);
                    }

                    match arc.op() {
                        // Concrete BVV case
                        BitVecOp::BVV(value) => {
                            ctx.bvv(value.extract(*low as usize, *high as usize - 1)?)
                        }

                        // Concat cases

                        // Extracting the entire left side
                        BitVecOp::Concat(lhs, rhs)
                            if *high == arc.size() - 1 && *low == rhs.size() =>
                        {
                            Ok(lhs.clone())
                        }
                        // Extracting the entire right side
                        BitVecOp::Concat(lhs, rhs) if *high == rhs.size() - 1 && *low == 0 => {
                            Ok(rhs.clone())
                        }
                        // Extracting a part of the left side
                        BitVecOp::Concat(lhs, rhs) if *low > rhs.size() => {
                            Ok(ctx.extract(lhs, *high - rhs.size(), *low - rhs.size())?)
                        }
                        // Extracting a part of the right side
                        BitVecOp::Concat(lhs, rhs) if *high <= rhs.size() => {
                            Ok(ctx.extract(rhs, *high, *low)?)
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
                BitVecOp::Concat(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            // Calculate the new length as the sum of both BitVec lengths
                            let new_length = value1.len() + value2.len();

                            // Shift the first value to the left to make space, then OR with the second value
                            let concatenated_value =
                                ((value1.clone() << value2.len())? | value2.clone())?;

                            // Return a new BitVec with the concatenated result and new length
                            ctx.bvv(BitVec::from_biguint_trunc(
                                &concatenated_value.to_biguint(),
                                new_length,
                            ))
                        }
                        _ => ctx.concat(&arc, &arc1),
                    }
                }
                BitVecOp::Reverse(arc) => {
                    simplify!(arc);

                    match arc.op() {
                        BitVecOp::BVV(value) => {
                            let reversed_bits = value.reverse_bytes()?;
                            ctx.bvv(reversed_bits)
                        }
                        _ => ctx.reverse(&arc),
                    }
                }
                BitVecOp::FpToIEEEBV(arc) => {
                    simplify!(arc);

                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Convert the floating-point value to its IEEE 754 bit representation
                            let ieee_bits = float.to_ieee_bits();
                            let bit_length = float.fsort().size() as usize;

                            // Create a BitVec with the IEEE 754 representation
                            ctx.bvv(
                                BitVec::from_biguint(&ieee_bits, bit_length)
                                    .expect("Failed to create BitVec from BigUint"),
                            )
                        }
                        _ => ctx.fp_to_ieeebv(&arc), // Fallback for non-concrete values
                    }
                }
                BitVecOp::FpToUBV(arc, bit_size, fprm) => {
                    simplify!(arc);

                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Convert the float to an unsigned integer representation (BigUint)
                            let unsigned_value =
                                float.to_unsigned_biguint().unwrap_or(BigUint::zero());

                            // Truncate or extend the result to fit within the specified bit size
                            let result_bitvec =
                                BitVec::from_biguint_trunc(&unsigned_value, *bit_size as usize);

                            ctx.bvv(result_bitvec)
                        }
                        _ => ctx.fp_to_ubv(&arc, *bit_size, fprm.clone()), // Fallback for non-concrete values
                    }
                }
                BitVecOp::FpToSBV(arc, bit_size, fprm) => {
                    simplify!(arc);

                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Convert the float to a signed integer representation (BigInt)
                            let signed_value = float.to_signed_bigint().unwrap_or(BigInt::zero());

                            // Convert the signed value to BigUint for BitVec construction
                            let unsigned_value =
                                signed_value.to_biguint().unwrap_or(BigUint::zero());

                            // Create a BitVec with the result, truncating or extending to fit within the specified bit size
                            let result_bitvec =
                                BitVec::from_biguint_trunc(&unsigned_value, *bit_size as usize);

                            ctx.bvv(result_bitvec)
                        }
                        _ => ctx.fp_to_sbv(&arc, *bit_size, fprm.clone()), // Fallback for non-concrete values
                    }
                }
                BitVecOp::StrLen(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        StringOp::StringV(value) => {
                            let length = value.len() as u64;
                            ctx.bvv(BitVec::from_prim_with_size(length, 64)?)
                        }
                        // _ => Err(ClarirsError::InvalidArguments),
                        _ => ctx.strlen(&arc), // Fallback to symbolic
                    }
                }
                BitVecOp::StrIndexOf(arc, arc1, arc2) => {
                    simplify!(arc, arc1, arc2); // Simplify all arguments

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
                        // _ => Err(ClarirsError::InvalidArguments), // Handle non-concrete cases
                        _ => ctx.strindexof(&arc, &arc1, &arc2), // Fallback to symbolic
                    }
                }
                BitVecOp::StrToBV(arc) => {
                    simplify!(arc);

                    match arc.op() {
                        StringOp::StringV(string) => {
                            // Attempt to parse the string as a decimal integer
                            let value = BigUint::from_str_radix(string, 10)
                                .or_else(|_| BigUint::from_str_radix(string, 16)) // Try hexadecimal if decimal fails
                                .or_else(|_| BigUint::from_str_radix(string, 2)) // Try binary if hexadecimal fails
                                .map_err(|_| ClarirsError::InvalidArguments)?; // Error if parsing fails

                            // Determine the bit length required to represent the number
                            let bit_length = value.bits() as usize;

                            // Convert the parsed value into a BitVec with the calculated bit length
                            let bitvec = BitVec::from_biguint_trunc(&value, bit_length);
                            ctx.bvv(bitvec)
                        }
                        _ => ctx.strtobv(&arc),
                    }
                }

                BitVecOp::If(arc, arc1, arc2) => todo!("bv if simplification"),
                BitVecOp::Annotated(arc, annotation) => todo!("bv annotation simplification"),
            }
        })
    }
}
