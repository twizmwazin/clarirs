use core::panic;
use std::ops::Not;

use clarirs_core::{
    algorithms::{
        dfs::{DfsResult, walk_dfs},
        simplify::extract_bitvec_child,
        walk_post_order,
    },
    ast::bitvec::BitVecOpExt,
    prelude::*,
};
use num_bigint::{BigInt, BigUint};

use crate::{StridedInterval, reduce::Reduce};

fn deconstruct_constraints<'c>(constraint: &BoolAst<'c>) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
    let mut results = Vec::new();
    walk_dfs(&constraint.clone().into(), |node| {
        if let Some(bool_node) = node.as_bool() {
            match bool_node.op() {
                // We are only interested in certain boolean operations
                BooleanOp::Eq(..)
                | BooleanOp::Neq(..)
                | BooleanOp::ULT(..)
                | BooleanOp::ULE(..)
                | BooleanOp::UGT(..)
                | BooleanOp::UGE(..)
                | BooleanOp::SLT(..)
                | BooleanOp::SLE(..)
                | BooleanOp::SGT(..)
                | BooleanOp::SGE(..) => {
                    results.push(bool_node.clone());
                    DfsResult::SkipChildren
                }

                _ => {
                    // For other boolean operations, we continue traversing
                    DfsResult::Continue
                }
            }
        } else {
            DfsResult::Continue
        }
    })?;
    Ok(results)
}

/// Takes a linear constraint like `2 > x` and inverts it to `x < 2`.
fn invert_linear_constraint<'c>(constraint: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
    let ctx = constraint.context();

    match constraint.op() {
        BooleanOp::Eq(lhs, rhs) => ctx.eq_(rhs, lhs),
        BooleanOp::Neq(lhs, rhs) => ctx.neq(rhs, lhs),
        BooleanOp::ULT(lhs, rhs) => ctx.ult(rhs, lhs),
        BooleanOp::ULE(lhs, rhs) => ctx.ule(rhs, lhs),
        BooleanOp::UGT(lhs, rhs) => ctx.ugt(rhs, lhs),
        BooleanOp::UGE(lhs, rhs) => ctx.uge(rhs, lhs),
        BooleanOp::SLT(lhs, rhs) => ctx.sge(rhs, lhs),
        BooleanOp::SLE(lhs, rhs) => ctx.sge(rhs, lhs),
        BooleanOp::SGT(lhs, rhs) => ctx.slt(rhs, lhs),
        BooleanOp::SGE(lhs, rhs) => ctx.sle(rhs, lhs),
        _ => Err(ClarirsError::InvalidArgumentsWithMessage(format!(
            "invert_linear_constraint called on non-linear constraint: {constraint:?}"
        ))),
    }
}

/// "Peels" off ops from the left-hand side to transfer to the right-hand side,
/// when possible.
///
/// For example, if the constraint is `x + 1 == y`, it will return `y - 1 == x`.
///
/// TODO: Lots of implementation!
fn peel_lhs_to_rhs<'c>(constraint: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
    let ctx = constraint.context();

    let lhs = extract_bitvec_child(&constraint.children(), 0)?;
    let rhs = extract_bitvec_child(&constraint.children(), 1)?;

    let (new_lhs, new_rhs, flip_sign): (BitVecAst<'c>, BitVecAst<'c>, bool) = match lhs.op() {
        // BitVecOp::Not(ast) => todo!(),
        // BitVecOp::And(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::Or(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::Xor(inner_lhs, inner_rhs) => todo!(),
        BitVecOp::Neg(ast) => (ast.clone(), ctx.neg(&rhs)?, true),
        BitVecOp::Add(inner_lhs, inner_rhs) => {
            // Determine which side is symbolic and which is concrete
            if inner_lhs.symbolic() && !inner_rhs.symbolic() {
                // lhs is symbolic, rhs is concrete: x + c -> x = rhs - c
                (inner_lhs.clone(), ctx.sub(&rhs, inner_rhs)?, false)
            } else if !inner_lhs.symbolic() && inner_rhs.symbolic() {
                // lhs is concrete, rhs is symbolic: c + x -> x = rhs - c
                (inner_rhs.clone(), ctx.sub(&rhs, inner_lhs)?, false)
            } else {
                panic!(
                    "Add operation has both sides symbolic or both concrete: lhs.symbolic()={}, rhs.symbolic()={}",
                    inner_lhs.symbolic(),
                    inner_rhs.symbolic()
                );
            }
        }
        BitVecOp::Sub(inner_lhs, inner_rhs) => {
            // For subtraction: lhs - rhs
            if inner_lhs.symbolic() && !inner_rhs.symbolic() {
                // x - c -> x = rhs + c
                (inner_lhs.clone(), ctx.add(&rhs, inner_rhs)?, false)
            } else if !inner_lhs.symbolic() && inner_rhs.symbolic() {
                // c - x -> x = c - rhs (note: this flips the sign)
                (inner_rhs.clone(), ctx.sub(inner_lhs, &rhs)?, true)
            } else {
                panic!(
                    "Sub operation has both sides symbolic or both concrete: lhs.symbolic()={}, rhs.symbolic()={}",
                    inner_lhs.symbolic(),
                    inner_rhs.symbolic()
                );
            }
        }
        // BitVecOp::Mul(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::UDiv(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::SDiv(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::URem(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::SRem(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::ShL(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::LShR(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::AShR(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::RotateLeft(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::RotateRight(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::ZeroExt(inner_lhs, inner_rhs) => todo!(),
        BitVecOp::ZeroExt(inner_ast, _num_zeroes) => {
            // For ZeroExt, we can try to eliminate it if the high bits of RHS are zero
            // For now, let's just return the inner expression and the original RHS
            (inner_ast.clone(), rhs.clone(), false)
        }
        BitVecOp::SignExt(inner_ast, _nbits) => {
            // For SignExt, we need to handle sign extension properly
            // SignExt(inner_ast, n) extends the sign bit of inner_ast by n bits

            // Check if we can safely remove the sign extension
            // This is only safe if the RHS value fits within the range of the inner expression
            // when interpreted as a signed value

            let inner_size = inner_ast.size();
            let extended_size = lhs.size();

            if inner_size == extended_size {
                // No actual extension, just return the inner expression
                (inner_ast.clone(), rhs.clone(), false)
            } else {
                // We need to check if RHS can be represented in the smaller bit width
                // For now, we'll extract the lower bits of RHS to match inner_ast size
                let ctx = constraint.context();
                let truncated_rhs = ctx.extract(&rhs, inner_size - 1, 0)?;
                (inner_ast.clone(), truncated_rhs, false)
            }
        }
        BitVecOp::Extract(ast, upper_bound, lower_bound) => {
            // For Extract(ast, upper, lower), the bounds are already constant u32 values
            let upper_val = *upper_bound;
            let lower_val = *lower_bound;

            // Extract width
            let extract_width = upper_val - lower_val + 1;

            // For Extract(x, upper, lower) == rhs, we need to find x such that
            // extracting bits [upper:lower] from x equals rhs

            // Handle the case where we're extracting the full width
            if lower_val == 0 && upper_val == ast.size() - 1 {
                // Extract of full width is just the original expression
                (ast.clone(), rhs.clone(), false)
            } else {
                // For partial extracts, we need to "reverse" the extract operation
                // Extract(x, upper, lower) == rhs means that bits [upper:lower] of x equal rhs
                //
                // To reverse this, we need to create a new RHS that represents the possible
                // values of x that would satisfy this constraint.
                //
                // If we have Extract(x, upper, lower) == rhs_val, then x can be any value
                // where bits [upper:lower] equal rhs_val and other bits can be anything.
                //
                // For now, we'll handle the simple case where we extract from the bottom
                if lower_val == 0 {
                    // Extract(x, upper, 0) == rhs means the bottom (upper+1) bits of x equal rhs
                    // The upper bits can be anything, so we need to zero-extend rhs to full width
                    let zero_ext_bits = ast.size() - extract_width;
                    if zero_ext_bits > 0 {
                        let new_rhs = ctx.zero_ext(&rhs, zero_ext_bits)?;
                        (ast.clone(), new_rhs, false)
                    } else {
                        (ast.clone(), rhs.clone(), false)
                    }
                } else {
                    // For extracts not starting from bit 0, we need more complex handling
                    // This would require creating a constraint that the extracted bits match
                    // while allowing other bits to be unconstrained
                    panic!(
                        "Extract operations not starting from bit 0 are not yet fully supported in peel_lhs_to_rhs"
                    );
                }
            }
        }
        // BitVecOp::Concat(inner_lhs, inner_rhs) => todo!(),
        // BitVecOp::Reverse(ast_node) => todo!(),
        BitVecOp::If(cond, true_expr, false_expr) => {
            // Handle If expressions by checking if the condition is concrete
            if cond.is_true() {
                // If condition is true, the If expression evaluates to the true branch
                (true_expr.clone(), rhs.clone(), false)
            } else if cond.is_false() {
                // If condition is false, the If expression evaluates to the false branch
                (false_expr.clone(), rhs.clone(), false)
            } else {
                // Condition is symbolic - not supported yet
                panic!(
                    "How do I handle {:?} in peel_lhs_to_rhs?\nFull constraint: {:?}",
                    cond, constraint
                );
            }
        }
        // BitVecOp::Union(ast_node, ast_node1) => todo!(),
        // BitVecOp::Intersection(ast_node, ast_node1) => todo!(),
        _ => panic!(
            "unsupported bit-vector operation in peel_lhs_to_rhs: {:?}",
            lhs.op()
        ),
    };

    match constraint.op() {
        BooleanOp::Eq(..) => ctx.eq_(&new_lhs, &new_rhs),
        BooleanOp::Neq(..) => ctx.neq(&new_lhs, &new_rhs),
        BooleanOp::ULT(..) => {
            if flip_sign {
                ctx.uge(&new_lhs, &new_rhs)
            } else {
                ctx.ult(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::ULE(..) => {
            if flip_sign {
                ctx.ugt(&new_lhs, &new_rhs)
            } else {
                ctx.ule(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::UGT(..) => {
            if flip_sign {
                ctx.ule(&new_lhs, &new_rhs)
            } else {
                ctx.ugt(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::UGE(..) => {
            if flip_sign {
                ctx.ult(&new_lhs, &new_rhs)
            } else {
                ctx.uge(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::SLT(..) => {
            if flip_sign {
                ctx.sge(&new_lhs, &new_rhs)
            } else {
                ctx.slt(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::SLE(..) => {
            if flip_sign {
                ctx.sgt(&new_lhs, &new_rhs)
            } else {
                ctx.sle(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::SGT(..) => {
            if flip_sign {
                ctx.sle(&new_lhs, &new_rhs)
            } else {
                ctx.sgt(&new_lhs, &new_rhs)
            }
        }
        BooleanOp::SGE(..) => {
            if flip_sign {
                ctx.slt(&new_lhs, &new_rhs)
            } else {
                ctx.sge(&new_lhs, &new_rhs)
            }
        }
        _ => panic!(),
    }
}

fn convert_simple_linear_constraint_to_si<'c>(
    expression: &BoolAst<'c>,
) -> Result<StridedInterval, ClarirsError> {
    Ok(match expression.op() {
        BooleanOp::Eq(_, rhs) => rhs.simplify()?.reduce()?,
        BooleanOp::Neq(_, rhs) => rhs.simplify()?.reduce()?.not(),
        BooleanOp::ULT(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (rhs_min, _) = rhs_si.get_unsigned_bounds();
            if rhs_min > BigUint::from(0u32) {
                StridedInterval::new(lhs.size(), 1u32.into(), 0u32.into(), &rhs_min - 1u32)
            } else {
                // If rhs_min is 0, then x < 0 is impossible for unsigned values
                StridedInterval::empty(lhs.size())
            }
        }
        BooleanOp::ULE(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (_, rhs_max) = rhs_si.get_unsigned_bounds();
            StridedInterval::new(lhs.size(), 1u32.into(), 0u32.into(), rhs_max)
        }
        BooleanOp::UGT(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (_, rhs_max) = rhs_si.get_unsigned_bounds();
            StridedInterval::new(
                lhs.size(),
                1u32.into(),
                &rhs_max + 1u32,
                (BigUint::from(1u32) << lhs.size()) - 1u32,
            )
        }
        BooleanOp::UGE(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (rhs_min, _) = rhs_si.get_unsigned_bounds();
            StridedInterval::new(
                lhs.size(),
                1u32.into(),
                rhs_min,
                (BigUint::from(1u32) << lhs.size()) - 1u32,
            )
        }
        BooleanOp::SLT(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (rhs_min, _) = rhs_si.get_unsigned_bounds();
            // For signed less than x < N, the valid range is from 0 to N-1
            // when N is positive (which is the case in the test)
            StridedInterval::new(
                lhs.size(),
                1u32.into(),
                0u32.into(),
                if rhs_min > BigUint::from(0u32) {
                    &rhs_min - 1u32
                } else {
                    (BigUint::from(1u32) << lhs.size()) - 1u32
                },
            )
        }
        BooleanOp::SLE(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (_, rhs_max) = rhs_si.get_signed_bounds();
            let signed_min = if lhs.size() > 0 {
                BigUint::from(1u32) << (lhs.size() - 1)
            } else {
                BigUint::from(0u32)
            };

            let rhs_max_uint = if rhs_max >= BigInt::from(0) {
                rhs_max.magnitude().clone()
            } else {
                let max_val = BigUint::from(1u32) << lhs.size();
                &max_val - rhs_max.magnitude()
            };

            StridedInterval::new(lhs.size(), 1u32.into(), signed_min, rhs_max_uint)
        }
        BooleanOp::SGT(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (_, rhs_max) = rhs_si.get_signed_bounds();
            // For signed greater than, valid range is from rhs_max+1 to signed max
            let signed_max = if lhs.size() > 0 {
                (BigUint::from(1u32) << (lhs.size() - 1)) - 1u32
            } else {
                BigUint::from(0u32)
            };

            let rhs_max_uint = if rhs_max >= BigInt::from(0) {
                rhs_max.magnitude().clone()
            } else {
                let max_val = BigUint::from(1u32) << lhs.size();
                &max_val - rhs_max.magnitude()
            };

            StridedInterval::new(lhs.size(), 1u32.into(), &rhs_max_uint + 1u32, signed_max)
        }
        BooleanOp::SGE(lhs, rhs) => {
            let rhs_si = rhs.simplify()?.reduce()?;
            let (rhs_min, _) = rhs_si.get_signed_bounds();
            let signed_max = if lhs.size() > 0 {
                (BigUint::from(1u32) << (lhs.size() - 1)) - 1u32
            } else {
                BigUint::from(0u32)
            };

            let rhs_min_uint = if rhs_min >= BigInt::from(0) {
                rhs_min.magnitude().clone()
            } else {
                let max_val = BigUint::from(1u32) << lhs.size();
                &max_val - rhs_min.magnitude()
            };

            StridedInterval::new(lhs.size(), 1u32.into(), rhs_min_uint, signed_max)
        }
        _ => panic!("unsupported linear constraint operation"),
    })
}

/// Linear constraints are of the form `lhs op rhs`, where `lhs` and `rhs` are
/// bit-vector expressions, `op` is a linear operation (like `Eq`, `Neq`, `ULT`, etc.).
fn linear_constraint_to_si<'c>(
    constraint: &BoolAst<'c>,
) -> Result<(BitVecAst<'c>, StridedInterval), ClarirsError> {
    // Special case: Check if we have an Add or Sub operation that might cause overflow/underflow
    // e.g., x + c <= bound or x - c <= bound
    if let Ok(special_si) = handle_add_sub_with_overflow(constraint) {
        return Ok(special_si);
    }

    // High level idea:
    // 1. Identify the side with the highest cardinality
    // NOTE: We use symbolic() as a proxy for high cardinality since VSA cardinality is broken for Add operations
    let lhs = extract_bitvec_child(&constraint.children(), 0)?;
    let rhs = extract_bitvec_child(&constraint.children(), 1)?;
    let lhs_symbolic = lhs.symbolic();
    let rhs_symbolic = rhs.symbolic();

    if lhs_symbolic && rhs_symbolic {
        panic!(
            "linear_constraint_to_si requires at least one side to be concrete, found: lhs symbolic = {}, rhs symbolic = {}",
            lhs_symbolic, rhs_symbolic
        );
    }

    // 2. Ensure symbolic side is on the left
    let mut expression = if rhs_symbolic && !lhs_symbolic {
        invert_linear_constraint(constraint)?
    } else {
        constraint.clone()
    };

    // 3. Strip all non-variable terms from the left side
    let mut iterations = 0;
    while !extract_bitvec_child(&expression.children(), 0)?.is_leaf() {
        expression = peel_lhs_to_rhs(&expression)?;
        iterations += 1;
        if iterations > 10 {
            panic!("Too many iterations in peeling, possible infinite loop");
        }
    }

    // 4. Convert to a strided interval
    let variable = extract_bitvec_child(&expression.children(), 0)?;
    let converted_si = convert_simple_linear_constraint_to_si(&expression)?;

    Ok((variable, converted_si))
}

/// Handle constraints involving Add or Sub operations that might cause overflow/underflow
/// e.g., x + c <= bound or x - c <= bound
fn handle_add_sub_with_overflow<'c>(
    constraint: &BoolAst<'c>,
) -> Result<(BitVecAst<'c>, StridedInterval), ClarirsError> {
    let lhs = extract_bitvec_child(&constraint.children(), 0)?;
    let rhs = extract_bitvec_child(&constraint.children(), 1)?;

    // Check if LHS is an Add or Sub operation
    match lhs.op() {
        BitVecOp::Add(add_lhs, add_rhs) => {
            // Check if one side is symbolic and the other is concrete
            let (var, constant) = if add_lhs.symbolic() && !add_rhs.symbolic() {
                (add_lhs, add_rhs)
            } else if !add_lhs.symbolic() && add_rhs.symbolic() {
                (add_rhs, add_lhs)
            } else {
                return Err(ClarirsError::UnsupportedOperation(
                    "Add with both sides symbolic or both concrete".to_string(),
                ));
            };

            // Check if RHS is concrete
            if !rhs.symbolic() {
                // We have: var + constant op rhs_value
                let constant_si = constant.simplify()?.reduce()?;
                let rhs_si = rhs.simplify()?.reduce()?;

                let (constant_val, _) = constant_si.get_unsigned_bounds();
                let (rhs_val, _) = rhs_si.get_unsigned_bounds();

                let bits = var.size();
                let max_val = (BigUint::from(1u32) << bits) - 1u32;

                match constraint.op() {
                    BooleanOp::ULE(..) => {
                        // var + constant <= rhs_val
                        // This is satisfied when (var + constant) mod 2^bits <= rhs_val

                        if rhs_val >= constant_val {
                            // Normal case exists: var in [0, rhs_val - constant]
                            let normal_upper = &rhs_val - &constant_val;

                            // Check if overflow case exists
                            let overflow_start = (BigUint::from(1u32) << bits) - &constant_val;

                            if overflow_start <= max_val {
                                // Overflow case exists
                                // Combined range: [overflow_start, max_val] ∪ [0, normal_upper]
                                // This can be represented as a wraparound interval: [overflow_start, normal_upper]
                                return Ok((
                                    var.clone(),
                                    StridedInterval::new(
                                        bits,
                                        1u32.into(),
                                        overflow_start,
                                        normal_upper,
                                    ),
                                ));
                            } else {
                                // Only normal case
                                return Ok((
                                    var.clone(),
                                    StridedInterval::new(
                                        bits,
                                        1u32.into(),
                                        0u32.into(),
                                        normal_upper,
                                    ),
                                ));
                            }
                        } else {
                            // No normal case, only overflow case
                            let overflow_start =
                                (BigUint::from(1u32) << bits) - &constant_val + &rhs_val + 1u32;
                            if overflow_start <= max_val {
                                return Ok((
                                    var.clone(),
                                    StridedInterval::new(
                                        bits,
                                        1u32.into(),
                                        overflow_start,
                                        max_val,
                                    ),
                                ));
                            } else {
                                // No solutions
                                return Ok((var.clone(), StridedInterval::empty(bits)));
                            }
                        }
                    }
                    _ => {
                        // For other operations, fall back to normal processing
                        return Err(ClarirsError::UnsupportedOperation(
                            "Unsupported operation in handle_add_sub_with_overflow for Add"
                                .to_string(),
                        ));
                    }
                }
            }
        }
        BitVecOp::Sub(sub_lhs, sub_rhs) => {
            // Check if LHS is symbolic and RHS is concrete
            if sub_lhs.symbolic() && !sub_rhs.symbolic() && !rhs.symbolic() {
                // We have: var - constant <= rhs_val
                let var = sub_lhs;
                let constant = sub_rhs;

                let constant_si = constant.simplify()?.reduce()?;
                let rhs_si = rhs.simplify()?.reduce()?;

                let (constant_val, _) = constant_si.get_unsigned_bounds();
                let (rhs_val, _) = rhs_si.get_unsigned_bounds();

                let bits = var.size();

                match constraint.op() {
                    BooleanOp::ULE(..) => {
                        // var - constant <= rhs_val
                        // Normal case: var >= constant and var - constant <= rhs_val
                        // So: constant <= var <= constant + rhs_val

                        // Underflow case: var < constant, so var - constant wraps around
                        // For this to be <= rhs_val, we need (2^bits + var - constant) <= rhs_val
                        // So: var <= rhs_val + constant - 2^bits
                        // This is only valid if rhs_val + constant >= 2^bits

                        let max_val = (BigUint::from(1u32) << bits) - 1u32;
                        let modulus = BigUint::from(1u32) << bits;

                        // Normal case upper bound
                        let normal_upper = if &constant_val + &rhs_val <= max_val {
                            &constant_val + &rhs_val
                        } else {
                            max_val.clone()
                        };

                        // Check if underflow case exists
                        let underflow_threshold = &constant_val + &rhs_val;
                        if underflow_threshold >= modulus {
                            // Underflow case exists: var in [0, underflow_threshold - 2^bits]
                            let underflow_upper = &underflow_threshold - &modulus;

                            // Combined range: [0, underflow_upper] ∪ [constant, normal_upper]
                            // This is a wraparound interval: [constant, underflow_upper]
                            return Ok((
                                var.clone(),
                                StridedInterval::new(
                                    bits,
                                    1u32.into(),
                                    constant_val.clone(),
                                    underflow_upper,
                                ),
                            ));
                        } else {
                            // Only normal case: [constant, normal_upper]
                            return Ok((
                                var.clone(),
                                StridedInterval::new(
                                    bits,
                                    1u32.into(),
                                    constant_val.clone(),
                                    normal_upper,
                                ),
                            ));
                        }
                    }
                    _ => {
                        return Err(ClarirsError::UnsupportedOperation(
                            "Unsupported operation in handle_add_sub_with_overflow for Sub"
                                .to_string(),
                        ));
                    }
                }
            }
        }
        _ => {}
    }

    Err(ClarirsError::UnsupportedOperation(
        "Not an Add or Sub operation with overflow potential".to_string(),
    ))
}

/// Collapse the strided intervals based on the boolean logic of the original
/// constraint.
fn collapse_si_replacements<'c>(
    original_constraint: &BoolAst<'c>,
    si_replacements: Vec<(BoolAst<'c>, StridedInterval)>,
) -> Result<StridedInterval, ClarirsError> {
    // Create a helper function to find the SI for a given constraint
    let find_si = |constraint: &BoolAst<'c>| -> Option<StridedInterval> {
        si_replacements
            .iter()
            .find(|(c, _)| c == constraint)
            .map(|(_, si)| si.clone())
    };

    Ok(walk_post_order::<Option<StridedInterval>>(
        original_constraint.into(),
        |ast, children| match ast {
            DynAst::Boolean(bool_node) => {
                match bool_node.op() {
                    BooleanOp::BoolS(..) => panic!(
                        "BoolS operation encountered in collapse_si_replacements, which is not supported"
                    ),
                    BooleanOp::BoolV(true) => {
                        // BoolV(true) means the constraint is always true, so we return a universal interval
                        Ok(Some(StridedInterval::top(64))) // FIXME: Use the correct size
                    }
                    BooleanOp::BoolV(false) => panic!(
                        "BoolV(false) encountered in collapse_si_replacements, which is UNSAT"
                    ),
                    BooleanOp::Not(..) => {
                        // For NOT, we need to negate the child SI
                        if let Some(child_si) = children.first().cloned().flatten() {
                            return Ok(Some(child_si.not()));
                        }
                        Ok(None)
                    }
                    BooleanOp::And(..) | BooleanOp::BoolEq(..) => {
                        // For AND, we need to intersect the children
                        if let Some(lhs) = children.first().cloned().flatten() {
                            if let Some(rhs) = children.get(1).cloned().flatten() {
                                return Ok(Some(lhs.intersection(&rhs)));
                            }
                        }
                        Ok(None)
                    }
                    BooleanOp::Or(..) => {
                        // For OR, we need to union the children
                        if let Some(lhs) = children.first().cloned().flatten() {
                            if let Some(rhs) = children.get(1).cloned().flatten() {
                                return Ok(Some(lhs.union(&rhs)));
                            }
                        }
                        Ok(None)
                    }
                    BooleanOp::Xor(..) | BooleanOp::BoolNeq(..) => todo!(),
                    BooleanOp::Eq(..)
                    | BooleanOp::Neq(..)
                    | BooleanOp::ULT(..)
                    | BooleanOp::ULE(..)
                    | BooleanOp::UGT(..)
                    | BooleanOp::UGE(..)
                    | BooleanOp::SLT(..)
                    | BooleanOp::SLE(..)
                    | BooleanOp::SGT(..)
                    | BooleanOp::SGE(..) => {
                        // For linear constraints, return the replacement SI
                        Ok(find_si(&bool_node))
                    }
                    BooleanOp::If(cond, _, _) => {
                        if cond.is_true() {
                            // If the condition is true, return the true branch
                            Ok(children.get(1).cloned().flatten())
                        } else if cond.is_false() {
                            // If the condition is false, return the false branch
                            Ok(children.get(2).cloned().flatten())
                        } else {
                            // Symbolic case is unsupported for now
                            Ok(None)
                        }
                    }
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        },
        &(),
    )?
    .unwrap())
}

pub fn constraint_to_si<'c>(
    constraint: &BoolAst<'c>,
) -> Result<(BitVecAst<'c>, StridedInterval), ClarirsError> {
    println!("constraint_to_si called with:\n{constraint:?}");
    let constraint_ = constraint.simplify()?;
    let constraint = &constraint_;
    println!("constraint has been simplified to:\n{constraint:?}");
    // if constraint.variables().len() != 1 {
    //     panic!(
    //         "constraint_to_si requires a single variable, found: {:?}",
    //         constraint.variables()
    //     );
    // }
    let variable_name = constraint.variables().iter().next().unwrap();

    // Special case: Handle If expressions in constraints
    if let Ok((var, si)) = handle_if_expression_constraint(constraint) {
        if let BitVecOp::BVS(name, _) = var.op() {
            if name == variable_name {
                return Ok((var, si));
            }
        }
    }

    // First, try to handle simple cases where the constraint is already a linear constraint
    if let Ok((var, si)) = linear_constraint_to_si(constraint) {
        if let BitVecOp::BVS(name, _) = var.op() {
            if name == variable_name {
                return Ok((var, si));
            }
        }
    }

    // Step 1: deconstruct constraints into a set of linear constraints
    let deconstructed_constraints = deconstruct_constraints(constraint)?;

    // Step 2: convert linear constraints into strided intervals
    let mut si_replacements: Vec<(BoolAst<'c>, StridedInterval)> = Vec::new();
    let mut variable_ast = None;

    for constraint_part in deconstructed_constraints {
        match linear_constraint_to_si(&constraint_part) {
            Ok((var, si)) => {
                // Check if this variable matches our expected variable by name
                if let BitVecOp::BVS(name, _) = var.op() {
                    if name == variable_name {
                        si_replacements.push((constraint_part, si));
                        if variable_ast.is_none() {
                            variable_ast = Some(var);
                        }
                    }
                }
            }
            Err(_) => {
                // If we can't convert this constraint, skip it
                continue;
            }
        }
    }

    // If we still haven't found the variable, create it from the constraint variables
    if variable_ast.is_none() && !si_replacements.is_empty() {
        let ctx = constraint.context();
        variable_ast = Some(ctx.bvs(variable_name, 32)?); // Assume 32-bit for now
    }

    let variable_ast = variable_ast.ok_or_else(|| {
        ClarirsError::UnsupportedOperation("Could not find variable in constraints".to_string())
    })?;

    // Step 3: Now, we need to combine these strided intervals using the boolean
    // logic of the original constraint.
    let result_si = if si_replacements.is_empty() {
        // If we have no SI replacements, try to convert the entire constraint
        convert_simple_linear_constraint_to_si(constraint)?
    } else {
        collapse_si_replacements(constraint, si_replacements)?
    };

    Ok((variable_ast, result_si))
}

/// Handle constraints involving If expressions
/// Pattern: ZeroExt(n, If(cond, true_val, false_val)) == 0
/// This means If(cond, true_val, false_val) == 0
fn handle_if_expression_constraint<'c>(
    constraint: &BoolAst<'c>,
) -> Result<(BitVecAst<'c>, StridedInterval), ClarirsError> {
    let lhs = extract_bitvec_child(&constraint.children(), 0)?;
    let rhs = extract_bitvec_child(&constraint.children(), 1)?;

    // Check if we have an equality constraint
    if !matches!(constraint.op(), BooleanOp::Eq(..)) {
        return Err(ClarirsError::UnsupportedOperation(
            "If expression constraints only support equality for now".to_string(),
        ));
    }

    // Check if LHS is a ZeroExt of an If expression
    let if_expr = match lhs.op() {
        BitVecOp::ZeroExt(inner, _) => {
            if matches!(inner.op(), BitVecOp::If(..)) {
                inner
            } else {
                return Err(ClarirsError::UnsupportedOperation(
                    "Not a ZeroExt of If expression".to_string(),
                ));
            }
        }
        BitVecOp::If(..) => &lhs,
        _ => {
            return Err(ClarirsError::UnsupportedOperation(
                "LHS is not an If expression or ZeroExt of If".to_string(),
            ));
        }
    };

    // Extract the condition and branches from the If expression
    let (condition, true_branch, false_branch) = match if_expr.op() {
        BitVecOp::If(cond, true_val, false_val) => (cond, true_val, false_val),
        _ => unreachable!(),
    };

    // Check if RHS is concrete
    if rhs.symbolic() {
        return Err(ClarirsError::UnsupportedOperation(
            "RHS must be concrete for If expression constraints".to_string(),
        ));
    }

    let rhs_si = rhs.simplify()?.reduce()?;
    let (rhs_val, _) = rhs_si.get_unsigned_bounds();

    // Check which branch equals the RHS value
    let true_si = true_branch.simplify()?.reduce()?;
    let false_si = false_branch.simplify()?.reduce()?;
    let (true_val, _) = true_si.get_unsigned_bounds();
    let (false_val, _) = false_si.get_unsigned_bounds();

    let ctx = constraint.context();

    // Determine which condition must be true
    let resulting_constraint = if true_val == rhs_val && false_val != rhs_val {
        // condition must be true
        condition.clone()
    } else if false_val == rhs_val && true_val != rhs_val {
        // condition must be false
        ctx.not(condition)?
    } else {
        return Err(ClarirsError::UnsupportedOperation(
            "Ambiguous If expression constraint".to_string(),
        ));
    };

    // Now convert the resulting constraint to SI
    constraint_to_si(&resulting_constraint)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_full_width_peel() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let value = ctx.bvv_prim(42u32)?;

        // Extract(x, 31, 0) == 42 (full width extract)
        let extracted = ctx.extract(&x, 31, 0)?;
        let constraint = ctx.eq_(&extracted, &value)?;

        // This should peel off the extract and return x == 42
        let peeled = peel_lhs_to_rhs(&constraint).unwrap();

        // Verify the result
        assert_eq!(peeled, ctx.eq_(&x, &value)?);

        Ok(())
    }

    #[test]
    fn test_extract_bottom_bits_peel() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let value = ctx.bvv_prim(42u8)?;

        // Extract(x, 7, 0) == 42 (bottom 8 bits)
        let extracted = ctx.extract(&x, 7, 0)?;
        let constraint = ctx.eq_(&extracted, &value)?;

        // This should peel off the extract and return x == ZeroExt(24, 42)
        let peeled = peel_lhs_to_rhs(&constraint).unwrap();

        // The expected RHS is ZeroExt(24, value)
        let expected_rhs = ctx.zero_ext(&value, 24)?;
        let expected = ctx.eq_(&x, &expected_rhs)?;

        assert_eq!(peeled, expected);

        Ok(())
    }

    #[test]
    fn test_constraint_to_si_with_extract() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let value = ctx.bvv_prim(100u32)?;

        // Extract(x, 31, 0) < 100 (full width extract with inequality)
        let extracted = ctx.extract(&x, 31, 0)?;
        let constraint = ctx.ult(&extracted, &value)?;

        // Convert to strided interval
        let (var, si) = constraint_to_si(&constraint)?;

        // Verify the variable is correct
        assert_eq!(var.op(), &BitVecOp::BVS("x".to_string(), 32));

        // Verify the strided interval represents [0, 99]
        let (min_val, max_val) = si.get_unsigned_bounds();
        assert_eq!(min_val, BigUint::from(0u32));
        assert_eq!(max_val, BigUint::from(99u32));

        Ok(())
    }

    #[test]
    fn test_if_expression_true_condition_peel() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let value = ctx.bvv_prim(42u32)?;

        // Create If(true, x, y) == 42
        let true_cond = ctx.boolv(true)?;
        let if_expr = ctx.if_(&true_cond, &x, &y)?;
        let constraint = ctx.eq_(&if_expr, &value)?;

        // This should peel off the if and return x == 42
        let peeled = peel_lhs_to_rhs(&constraint)?;

        // Verify the result
        let expected = ctx.eq_(&x, &value)?;
        assert_eq!(peeled, expected);

        Ok(())
    }

    #[test]
    fn test_if_expression_false_condition_peel() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let value = ctx.bvv_prim(42u32)?;

        // Create If(false, x, y) == 42
        let false_cond = ctx.boolv(false)?;
        let if_expr = ctx.if_(&false_cond, &x, &y)?;
        let constraint = ctx.eq_(&if_expr, &value)?;

        // This should peel off the if and return y == 42
        let peeled = peel_lhs_to_rhs(&constraint)?;

        // Verify the result
        let expected = ctx.eq_(&y, &value)?;
        assert_eq!(peeled, expected);

        Ok(())
    }

    #[test]
    #[should_panic(expected = "If expressions with symbolic conditions are not yet supported")]
    fn test_if_expression_symbolic_condition_peel_panics() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        let z = ctx.bools("z").unwrap(); // symbolic condition
        let value = ctx.bvv_prim(42u32).unwrap();

        // Create If(z, x, y) == 42 where z is symbolic
        let if_expr = ctx.if_(&z, &x, &y).unwrap();
        let constraint = ctx.eq_(&if_expr, &value).unwrap();

        // This should panic
        peel_lhs_to_rhs(&constraint).unwrap();
    }

    #[test]
    fn test_constraint_to_si_with_if_expression() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let value = ctx.bvv_prim(100u32)?;

        // Create If(true, x, y) < 100
        let true_cond = ctx.boolv(true)?;
        let if_expr = ctx.if_(&true_cond, &x, &y)?;
        let constraint = ctx.ult(&if_expr, &value)?;

        // Convert to strided interval
        let (var, si) = constraint_to_si(&constraint)?;

        // Verify the variable is x (since condition is true)
        assert_eq!(var.op(), &BitVecOp::BVS("x".to_string(), 32));

        // Verify the strided interval represents [0, 99]
        let (min_val, max_val) = si.get_unsigned_bounds();
        assert_eq!(min_val, BigUint::from(0u32));
        assert_eq!(max_val, BigUint::from(99u32));

        Ok(())
    }
}
