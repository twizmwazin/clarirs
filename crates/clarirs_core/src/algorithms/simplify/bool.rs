use ahash::HashSet;

use super::SimplifyError;
use crate::{ast::bitvec::BitVecOpExt, prelude::*};

pub(crate) fn simplify_bool<'c>(
    state: &mut super::SimplifyState<'c>,
) -> Result<BoolAst<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let bool_ast = state.expr.clone().into_bool().unwrap();

    match bool_ast.op() {
        BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => Ok(bool_ast),
        BooleanOp::Not(..) => {
            let arc = state.get_bool_simplified(0)?;

            match arc.op() {
                BooleanOp::Not(arc) => Ok(arc.clone()),
                BooleanOp::BoolV(v) => Ok(ctx.boolv(!v)?),

                BooleanOp::Eq(lhs, rhs) => Ok(ctx.neq(lhs.clone(), rhs.clone())?),

                // !(a > b)  ==>  a <= b
                BooleanOp::UGT(lhs, rhs) => state.rerun(ctx.ule(lhs.clone(), rhs.clone())?),
                // !(a >= b)  ==>  a < b
                BooleanOp::UGE(lhs, rhs) => state.rerun(ctx.ult(lhs.clone(), rhs.clone())?),
                // !(a < b)  ==>  a >= b
                BooleanOp::ULT(lhs, rhs) => state.rerun(ctx.uge(lhs.clone(), rhs.clone())?),
                // !(a <= b)  ==>  a > b
                BooleanOp::ULE(lhs, rhs) => state.rerun(ctx.ugt(lhs.clone(), rhs.clone())?),
                // !(a s> b)  ==>  a s<= b
                BooleanOp::SGT(lhs, rhs) => state.rerun(ctx.sle(lhs.clone(), rhs.clone())?),
                // !(a s>= b)  ==>  a s< b
                BooleanOp::SGE(lhs, rhs) => state.rerun(ctx.slt(lhs.clone(), rhs.clone())?),
                // !(a s< b)  ==>  a s>= b
                BooleanOp::SLT(lhs, rhs) => state.rerun(ctx.sge(lhs.clone(), rhs.clone())?),
                // !(a s<= b)  ==>  a s> b
                BooleanOp::SLE(lhs, rhs) => state.rerun(ctx.sgt(lhs.clone(), rhs.clone())?),

                _ => Ok(ctx.not(arc)?),
            }
        }
        BooleanOp::And(args) => {
            let available_args = (0..args.len())
                .map(|i| state.get_bool_available(i))
                .collect::<Result<Vec<_>, _>>()?;

            // Identity simplification
            if available_args
                .iter()
                .any(|arg| matches!(arg.op(), BooleanOp::BoolV(false)))
            {
                return Ok(ctx.false_()?);
            }

            // Absorption simplification
            let mut seen = HashSet::default();
            let absorbed_args = available_args
                .into_iter()
                .filter(|arg| !matches!(arg.op(), BooleanOp::BoolV(true)))
                .filter(|arg| {
                    if seen.contains(&arg.hash()) {
                        false
                    } else {
                        seen.insert(arg.hash());
                        true
                    }
                })
                .collect::<Vec<_>>();

            if absorbed_args.is_empty() {
                return Ok(ctx.true_()?);
            }
            if absorbed_args.len() == 1 {
                return state.rerun(absorbed_args[0].clone());
            }

            // x & !x == false
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    if let BooleanOp::Not(neg) = absorbed_args[i].op() {
                        if neg == &absorbed_args[j] {
                            return Ok(ctx.false_()?);
                        }
                    }
                    if let BooleanOp::Not(neg) = absorbed_args[j].op() {
                        if neg == &absorbed_args[i] {
                            return Ok(ctx.false_()?);
                        }
                    }
                }
            }

            // All of the comparisons
            // ex x == K & x != K  ==>  false
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    match (absorbed_args[i].op(), absorbed_args[j].op()) {
                        (BooleanOp::Eq(var1, val1), BooleanOp::Neq(var2, val2))
                        | (BooleanOp::Neq(var2, val2), BooleanOp::Eq(var1, val1))
                        | (BooleanOp::ULT(var1, val1), BooleanOp::UGE(var2, val2))
                        | (BooleanOp::UGE(var2, val2), BooleanOp::ULT(var1, val1))
                        | (BooleanOp::ULE(var1, val1), BooleanOp::UGT(var2, val2))
                        | (BooleanOp::UGT(var2, val2), BooleanOp::ULE(var1, val1))
                        | (BooleanOp::SLT(var1, val1), BooleanOp::SGE(var2, val2))
                        | (BooleanOp::SGE(var2, val2), BooleanOp::SLT(var1, val1))
                        | (BooleanOp::SLE(var1, val1), BooleanOp::SGT(var2, val2))
                        | (BooleanOp::SGT(var2, val2), BooleanOp::SLE(var1, val1))
                            if var1 == var2 && val1 == val2 =>
                        {
                            return Ok(ctx.false_()?);
                        }
                        _ => {}
                    }
                }
            }

            if absorbed_args.len() != args.len() {
                return state.rerun(ctx.and(absorbed_args)?);
            }

            let simplified_args = (0..args.len())
                .map(|i| state.get_bool_simplified(i))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ctx.and(simplified_args)?)
        }
        BooleanOp::Or(args) => {
            let available_args = (0..args.len())
                .map(|i| state.get_bool_available(i))
                .collect::<Result<Vec<_>, _>>()?;

            // Identity simplification
            if available_args
                .iter()
                .any(|arg| matches!(arg.op(), BooleanOp::BoolV(true)))
            {
                return Ok(ctx.true_()?);
            }

            // Absorption simplification
            let mut seen = HashSet::default();
            let absorbed_args = available_args
                .into_iter()
                .filter(|arg| !matches!(arg.op(), BooleanOp::BoolV(false)))
                .filter(|arg| {
                    if seen.contains(&arg.hash()) {
                        false
                    } else {
                        seen.insert(arg.hash());
                        true
                    }
                })
                .collect::<Vec<_>>();

            if absorbed_args.is_empty() {
                return Ok(ctx.false_()?);
            }
            if absorbed_args.len() == 1 {
                return state.rerun(absorbed_args[0].clone());
            }

            // x | !x == true
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    if let BooleanOp::Not(neg) = absorbed_args[i].op() {
                        if neg == &absorbed_args[j] {
                            return Ok(ctx.true_()?);
                        }
                    }
                    if let BooleanOp::Not(neg) = absorbed_args[j].op() {
                        if neg == &absorbed_args[i] {
                            return Ok(ctx.true_()?);
                        }
                    }
                }
            }

            // All of the comparisons
            // ex x == K | x != K  ==>  true
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    match (absorbed_args[i].op(), absorbed_args[j].op()) {
                        (BooleanOp::Eq(var1, val1), BooleanOp::Neq(var2, val2))
                        | (BooleanOp::Neq(var2, val2), BooleanOp::Eq(var1, val1))
                        | (BooleanOp::ULT(var1, val1), BooleanOp::UGE(var2, val2))
                        | (BooleanOp::UGE(var2, val2), BooleanOp::ULT(var1, val1))
                        | (BooleanOp::ULE(var1, val1), BooleanOp::UGT(var2, val2))
                        | (BooleanOp::UGT(var2, val2), BooleanOp::ULE(var1, val1))
                        | (BooleanOp::SLT(var1, val1), BooleanOp::SGE(var2, val2))
                        | (BooleanOp::SGE(var2, val2), BooleanOp::SLT(var1, val1))
                        | (BooleanOp::SLE(var1, val1), BooleanOp::SGT(var2, val2))
                        | (BooleanOp::SGT(var2, val2), BooleanOp::SLE(var1, val1))
                            if var1 == var2 && val1 == val2 =>
                        {
                            return Ok(ctx.true_()?);
                        }
                        _ => {}
                    }
                }
            }

            if absorbed_args.len() != args.len() {
                return state.rerun(ctx.or(absorbed_args)?);
            }

            let simplified_args = (0..args.len())
                .map(|i| state.get_bool_simplified(i))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ctx.or(simplified_args)?)
        }
        BooleanOp::Xor(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs ^ *rhs)?),
                (BooleanOp::BoolV(true), _) => Ok(ctx.not(state.get_bool_simplified(1)?)?),
                (_, BooleanOp::BoolV(true)) => Ok(ctx.not(state.get_bool_simplified(0)?)?),
                (BooleanOp::BoolV(false), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(false)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.true_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.true_()?),
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => state.rerun(ctx.xor(lhs, rhs)?),
                _ if early_lhs == early_rhs => Ok(ctx.false_()?),
                _ => Ok(ctx.xor(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::BoolEq(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => Ok(ctx.boolv(arc == arc1)?),
                (BooleanOp::BoolV(true), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(true)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::BoolV(false), _) => Ok(ctx.not(state.get_bool_simplified(1)?)?),
                (_, BooleanOp::BoolV(false)) => Ok(ctx.not(state.get_bool_simplified(0)?)?),
                (BooleanOp::BoolS(name1), BooleanOp::BoolS(name2)) if name1 == name2 => {
                    Ok(ctx.true_()?)
                }
                _ => Ok(ctx.eq_(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::BoolNeq(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                (BooleanOp::BoolV(true), _) => Ok(ctx.not(state.get_bool_simplified(1)?)?),
                (_, BooleanOp::BoolV(true)) => Ok(ctx.not(state.get_bool_simplified(0)?)?),
                (BooleanOp::BoolV(false), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(false)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::BoolS(name1), BooleanOp::BoolS(name2)) if name1 == name2 => {
                    Ok(ctx.false_()?)
                }
                _ => Ok(ctx.neq(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::Eq(..) => {
            let early_lhs = state.get_bv_available(0)?;
            let early_rhs = state.get_bv_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc == arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (BitVecOp::And(lhs_and, mask), BitVecOp::BVV(bvv))
                | (BitVecOp::And(mask, lhs_and), BitVecOp::BVV(bvv))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.eq_(
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }

                // (ite cond 1 0) == 0  ==>  !cond
                (BitVecOp::ITE(cond, then_val, else_val), BitVecOp::BVV(val))
                | (BitVecOp::BVV(val), BitVecOp::ITE(cond, then_val, else_val))
                    if val.is_zero() =>
                {
                    if let (BitVecOp::BVV(then_bvv), BitVecOp::BVV(else_bvv)) =
                        (then_val.op(), else_val.op())
                    {
                        if then_bvv.is_one() && else_bvv.is_zero() {
                            // (ite cond 1 0) == 0  ==>  !cond
                            return state.rerun(ctx.not(cond.clone())?);
                        } else if then_bvv.is_zero() && else_bvv.is_one() {
                            // (ite cond 0 1) == 0  ==>  cond
                            return state.rerun(cond.clone());
                        }
                    }
                    Ok(ctx.eq_(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?)
                }

                // (ite cond 1 0) == 1  ==>  cond
                (BitVecOp::ITE(cond, then_val, else_val), BitVecOp::BVV(val))
                | (BitVecOp::BVV(val), BitVecOp::ITE(cond, then_val, else_val))
                    if val.is_one() =>
                {
                    if let (BitVecOp::BVV(then_bvv), BitVecOp::BVV(else_bvv)) =
                        (then_val.op(), else_val.op())
                    {
                        if then_bvv.is_one() && else_bvv.is_zero() {
                            // (ite cond 1 0) == 1  ==>  cond
                            return state.rerun(cond.clone());
                        } else if then_bvv.is_zero() && else_bvv.is_one() {
                            // (ite cond 0 1) == 1  ==>  !cond
                            return state.rerun(ctx.not(cond.clone())?);
                        }
                    }
                    Ok(ctx.eq_(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?)
                }

                _ => Ok(ctx.eq_(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?),
            }
        }
        BooleanOp::Neq(..) => {
            let early_lhs = state.get_bv_available(0)?;
            let early_rhs = state.get_bv_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (BitVecOp::And(lhs_and, mask), BitVecOp::BVV(bvv))
                | (BitVecOp::And(mask, lhs_and), BitVecOp::BVV(bvv))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.neq(
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }

                // (ite cond 1 0) != 0  ==>  cond
                (BitVecOp::ITE(cond, then_val, else_val), BitVecOp::BVV(val))
                | (BitVecOp::BVV(val), BitVecOp::ITE(cond, then_val, else_val))
                    if val.is_zero() =>
                {
                    if let (BitVecOp::BVV(then_bvv), BitVecOp::BVV(else_bvv)) =
                        (then_val.op(), else_val.op())
                    {
                        if then_bvv.is_one() && else_bvv.is_zero() {
                            // (ite cond 1 0) != 0  ==>  cond
                            return state.rerun(cond.clone());
                        } else if then_bvv.is_zero() && else_bvv.is_one() {
                            // (ite cond 0 1) != 0  ==>  !cond
                            return state.rerun(ctx.not(cond.clone())?);
                        }
                    }
                    Ok(ctx.neq(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?)
                }

                // (ite cond 1 0) != 1  ==>  !cond
                (BitVecOp::ITE(cond, then_val, else_val), BitVecOp::BVV(val))
                | (BitVecOp::BVV(val), BitVecOp::ITE(cond, then_val, else_val))
                    if val.is_one() =>
                {
                    if let (BitVecOp::BVV(then_bvv), BitVecOp::BVV(else_bvv)) =
                        (then_val.op(), else_val.op())
                    {
                        if then_bvv.is_one() && else_bvv.is_zero() {
                            // (ite cond 1 0) != 1  ==>  !cond
                            return state.rerun(ctx.not(cond.clone())?);
                        } else if then_bvv.is_zero() && else_bvv.is_one() {
                            // (ite cond 0 1) != 1  ==>  cond
                            return state.rerun(cond.clone());
                        }
                    }
                    Ok(ctx.neq(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?)
                }

                _ => Ok(ctx.neq(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?),
            }
        }
        BooleanOp::ULT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc < arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (BitVecOp::And(lhs_and, mask), BitVecOp::BVV(bvv))
                | (BitVecOp::And(mask, lhs_and), BitVecOp::BVV(bvv))
                | (BitVecOp::BVV(bvv), BitVecOp::And(lhs_and, mask))
                | (BitVecOp::BVV(bvv), BitVecOp::And(mask, lhs_and))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ult(
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }

                // If one side is a = ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (BitVecOp::ZeroExt(innner, ext_size), BitVecOp::BVV(outer))
                | (BitVecOp::BVV(outer), BitVecOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ult(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (BitVecOp::ZeroExt(inner_lhs, _), BitVecOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.ult(inner_lhs.clone(), inner_rhs.clone())?)
                }

                _ => Ok(ctx.ult(arc, arc1)?),
            }
        }
        BooleanOp::ULE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc <= arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (BitVecOp::And(lhs_and, mask), BitVecOp::BVV(bvv))
                | (BitVecOp::And(mask, lhs_and), BitVecOp::BVV(bvv))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ule(
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (BitVecOp::BVV(bvv), BitVecOp::And(lhs_and, mask))
                | (BitVecOp::BVV(bvv), BitVecOp::And(mask, lhs_and))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ule(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a = ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (BitVecOp::ZeroExt(innner, ext_size), BitVecOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ule(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (BitVecOp::BVV(outer), BitVecOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ule(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (BitVecOp::ZeroExt(inner_lhs, _), BitVecOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.ule(inner_lhs.clone(), inner_rhs.clone())?)
                }

                _ => Ok(ctx.ule(arc, arc1)?),
            }
        }
        BooleanOp::UGT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc > arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (BitVecOp::And(lhs_and, mask), BitVecOp::BVV(bvv))
                | (BitVecOp::And(mask, lhs_and), BitVecOp::BVV(bvv))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ugt(
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (BitVecOp::BVV(bvv), BitVecOp::And(lhs_and, mask))
                | (BitVecOp::BVV(bvv), BitVecOp::And(mask, lhs_and))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ugt(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a = ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (BitVecOp::ZeroExt(innner, ext_size), BitVecOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ugt(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (BitVecOp::BVV(outer), BitVecOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ugt(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (BitVecOp::ZeroExt(inner_lhs, _), BitVecOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.ugt(inner_lhs.clone(), inner_rhs.clone())?)
                }

                _ => Ok(ctx.ugt(arc, arc1)?),
            }
        }
        BooleanOp::UGE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc >= arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (BitVecOp::And(lhs_and, mask), BitVecOp::BVV(bvv))
                | (BitVecOp::And(mask, lhs_and), BitVecOp::BVV(bvv))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.uge(
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (BitVecOp::BVV(bvv), BitVecOp::And(lhs_and, mask))
                | (BitVecOp::BVV(bvv), BitVecOp::And(mask, lhs_and))
                    if {
                        if let BitVecOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask().is_some()
                        } else {
                            false
                        }
                    } =>
                {
                    let (mask_high, mask_low) = if let BitVecOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.uge(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a = ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (BitVecOp::ZeroExt(innner, ext_size), BitVecOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.uge(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (BitVecOp::BVV(outer), BitVecOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.uge(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (BitVecOp::ZeroExt(inner_lhs, _), BitVecOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.uge(inner_lhs.clone(), inner_rhs.clone())?)
                }

                _ => Ok(ctx.uge(arc, arc1)?),
            }
        }
        BooleanOp::SLT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_lt(arc1))?),
                _ => Ok(ctx.slt(arc, arc1)?),
            }
        }
        BooleanOp::SLE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_le(arc1))?),
                _ => Ok(ctx.sle(arc, arc1)?),
            }
        }
        BooleanOp::SGT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_gt(arc1))?),
                _ => Ok(ctx.sgt(arc, arc1)?),
            }
        }
        BooleanOp::SGE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_ge(arc1))?),
                _ => Ok(ctx.sge(arc, arc1)?),
            }
        }
        BooleanOp::FpEq(..) => {
            let early_lhs = state.get_fp_available(0)?;
            let early_rhs = state.get_fp_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.compare_fp(arc1))?),
                _ => Ok(ctx.fp_eq(state.get_fp_simplified(0)?, state.get_fp_simplified(1)?)?),
            }
        }
        BooleanOp::FpNeq(..) => {
            let early_lhs = state.get_fp_available(0)?;
            let early_rhs = state.get_fp_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(!arc.compare_fp(arc1))?),
                _ => Ok(ctx.fp_neq(state.get_fp_simplified(0)?, state.get_fp_simplified(1)?)?),
            }
        }
        BooleanOp::FpLt(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.lt(arc1))?),
                _ => Ok(ctx.fp_lt(arc, arc1)?),
            }
        }
        BooleanOp::FpLeq(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.leq(arc1))?),
                _ => Ok(ctx.fp_leq(arc, arc1)?),
            }
        }
        BooleanOp::FpGt(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.gt(arc1))?),
                _ => Ok(ctx.fp_gt(arc, arc1)?),
            }
        }
        BooleanOp::FpGeq(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.geq(arc1))?),
                _ => Ok(ctx.fp_geq(arc, arc1)?),
            }
        }
        BooleanOp::FpIsNan(..) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(arc) => Ok(ctx.boolv(arc.is_nan())?),
                _ => Ok(ctx.fp_is_nan(arc)?),
            }
        }
        BooleanOp::FpIsInf(..) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(arc) => Ok(ctx.boolv(arc.is_infinity())?),
                _ => Ok(ctx.fp_is_inf(arc)?),
            }
        }
        BooleanOp::StrContains(..) => {
            let (arc, arc1) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` contains `substring`
                (StringOp::StringV(input_string), StringOp::StringV(substring)) => {
                    Ok(ctx.boolv(input_string.contains(substring))?)
                }
                _ => Ok(ctx.str_contains(arc, arc1)?),
            }
        }
        BooleanOp::StrPrefixOf(..) => {
            let (arc, arc1) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` starts with `prefix substring`
                (StringOp::StringV(prefix), StringOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.starts_with(prefix))?)
                }
                _ => Ok(ctx.str_prefix_of(arc, arc1)?),
            }
        }
        BooleanOp::StrSuffixOf(..) => {
            let (arc, arc1) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` ends with `suffix substring`
                (StringOp::StringV(suffix), StringOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.ends_with(suffix))?)
                }
                _ => Ok(ctx.str_suffix_of(arc, arc1)?),
            }
        }
        BooleanOp::StrIsDigit(..) => {
            let arc = state.get_string_simplified(0)?;
            match arc.op() {
                StringOp::StringV(input_string) => {
                    if input_string.is_empty() {
                        return Ok(ctx.boolv(false)?);
                    }
                    // is_numeric() is Unicode-aware and will also return true for non-ASCII numeric characters like Z3
                    Ok(ctx.boolv(input_string.chars().all(|c| c.is_numeric()))?)
                }
                _ => Ok(ctx.str_is_digit(arc)?),
            }
        }
        BooleanOp::StrEq(..) => {
            let early_lhs = state.get_string_available(0)?;
            let early_rhs = state.get_string_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => Ok(ctx.boolv(str1 == str2)?),
                _ => Ok(ctx.str_eq(
                    state.get_string_simplified(0)?,
                    state.get_string_simplified(1)?,
                )?),
            }
        }
        BooleanOp::StrNeq(..) => {
            let early_lhs = state.get_string_available(0)?;
            let early_rhs = state.get_string_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => Ok(ctx.boolv(str1 != str2)?),
                _ => Ok(ctx.str_neq(
                    state.get_string_simplified(0)?,
                    state.get_string_simplified(1)?,
                )?),
            }
        }

        BooleanOp::ITE(..) => {
            let cond = state.get_bool_simplified(0)?;
            let early_then = state.get_bool_available(1)?;
            let early_else = state.get_bool_available(2)?;

            match (cond.op(), early_then.op(), early_else.op()) {
                // Concrete condition cases
                (BooleanOp::BoolV(true), _, _) => state.get_bool_simplified(1),
                (BooleanOp::BoolV(false), _, _) => state.get_bool_simplified(2),

                // Same branch cases
                (_, _, _) if early_then == early_else => state.get_bool_simplified(1),

                // Known then/else cases
                (_, BooleanOp::BoolV(true), BooleanOp::BoolV(false)) => Ok(cond.clone()),
                (_, BooleanOp::BoolV(false), BooleanOp::BoolV(true)) => Ok(ctx.not(cond)?),

                // When condition equals one branch with concrete other branch
                (cond_op, BooleanOp::BoolV(true), else_op) if else_op == cond_op => {
                    Ok(cond.clone())
                }
                (cond_op, BooleanOp::BoolV(false), else_op) if else_op == cond_op => {
                    Ok(ctx.false_()?)
                }
                (cond_op, then_op, BooleanOp::BoolV(true)) if then_op == cond_op => {
                    Ok(ctx.true_()?)
                }
                (cond_op, then_op, BooleanOp::BoolV(false)) if then_op == cond_op => {
                    Ok(cond.clone())
                }

                // Default case
                _ => Ok(ctx.ite(
                    cond,
                    state.get_bool_simplified(1)?,
                    state.get_bool_simplified(2)?,
                )?),
            }
        }
    }
}
