#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use crate::{cache::Cache, prelude::*};

impl<'c> AstNode<'c> {
    pub fn simplify(self: &Arc<Self>) -> Result<AstRef<'c>, ClarirsError> {
        self.simplify_ext(true, false)
    }

    pub fn simplify_ext(
        self: &Arc<Self>,
        respect_annotations: bool,
        error_on_dbz: bool,
    ) -> Result<AstRef<'c>, ClarirsError> {
        simplify(self, respect_annotations, error_on_dbz)
    }
}

#[derive(thiserror::Error, Debug)]
enum SimplifyError<'c> {
    #[error("Missing child at index {0}")]
    MissingChild(usize),
    #[error("Missing {} children", .0.len())]
    MissingChildren(Vec<usize>),
    #[error("Re-run simplification")]
    #[allow(dead_code)]
    ReRun(AstRef<'c>),
    #[error("Clarirs error: {0}")]
    Error(ClarirsError),
}

impl<T> From<T> for SimplifyError<'_>
where
    ClarirsError: From<T>,
{
    fn from(value: T) -> Self {
        SimplifyError::Error(ClarirsError::from(value))
    }
}

struct SimplifyState<'c> {
    expr: AstRef<'c>,
    children: Vec<Option<AstRef<'c>>>,
    last_missed_child: Option<usize>,
}

impl<'c> SimplifyState<'c> {
    fn new(expr: AstRef<'c>) -> Self {
        Self {
            expr: expr.clone(),
            children: vec![None; expr.child_iter().count()],
            last_missed_child: None,
        }
    }

    /// Get the simplified child at the given index, or return an error if it is missing.
    fn get_child_simplified(&mut self, index: usize) -> Result<AstRef<'c>, SimplifyError<'c>> {
        if let Some(child) = &self.children[index] {
            Ok(child.clone())
        } else {
            self.last_missed_child = Some(index);
            Err(SimplifyError::MissingChild(index))
        }
    }

    /// Return simplified versions of all children in one shot. If any are
    /// missing, returns `MissingChildren` listing every missing index so the
    /// main simplify loop can schedule them in one batch. This is crucial for
    /// n-ary ops (like Concat) with many children: fetching them one at a
    /// time causes quadratic re-runs of simplify_inner.
    fn get_all_simplified(&self) -> Result<Vec<AstRef<'c>>, SimplifyError<'c>> {
        let missing: Vec<usize> = self
            .children
            .iter()
            .enumerate()
            .filter_map(|(i, c)| c.is_none().then_some(i))
            .collect();
        if !missing.is_empty() {
            return Err(SimplifyError::MissingChildren(missing));
        }
        Ok(self.children.iter().map(|c| c.clone().unwrap()).collect())
    }

    /// Get the best available child: if we have a simplified version, return that,
    /// otherwise return the original child.
    fn get_child_available(&self, index: usize) -> AstRef<'c> {
        if let Some(child) = &self.children[index] {
            child.clone()
        } else {
            self.expr.get_child(index).unwrap()
        }
    }

    fn rerun(&self, new_ast: AstRef<'c>) -> Result<AstRef<'c>, SimplifyError<'c>> {
        Err(SimplifyError::ReRun(new_ast))
    }
}

fn simplify_inner<'c>(
    state: &mut SimplifyState<'c>,
    error_on_dbz: bool,
) -> Result<AstRef<'c>, SimplifyError<'c>> {
    let expr = &state.expr.clone();
    expr.context()
        .simplification_cache
        .get_or_insert(state.expr.hash(), || match expr.ast_type() {
            AstType::Bool => simplify_bool(state),
            AstType::BitVec(_) => simplify_bv(state, error_on_dbz),
            AstType::Float(_) => simplify_float(state),
            AstType::String => simplify_string(state),
        })
}

fn simplify<'c>(
    ast: &AstRef<'c>,
    respect_annotations: bool,
    error_on_dbz: bool,
) -> Result<AstRef<'c>, ClarirsError> {
    let mut work_stack: Vec<SimplifyState<'c>> = Vec::new();
    let mut last_result: Option<AstRef<'c>> = None;

    work_stack.push(SimplifyState::new(ast.clone()));

    while let Some(mut state) = work_stack.pop() {
        if let Some(missed_index) = state.last_missed_child {
            // We missed a child last time, so we need to get the last result and set it as the child
            state.children[missed_index] = Some(last_result.take().unwrap());
            state.last_missed_child = None;
        }

        let blocked = state
            .expr
            .annotations()
            .iter()
            .any(|a| !a.eliminatable() && !a.relocatable())
            || !state.expr.simplifiable();
        let should_simplify = !respect_annotations || !blocked;
        if should_simplify {
            let inner_result = simplify_inner(&mut state, error_on_dbz);
            match inner_result {
                Ok(result) => {
                    let relocatable_annotations: Vec<Annotation> = state
                        .expr
                        .annotations()
                        .iter()
                        .filter(|a| a.relocatable())
                        .cloned()
                        .collect();
                    let annotated = state
                        .expr
                        .context()
                        .annotate(&result, relocatable_annotations)?;

                    // Cache the mapping from the original expression to the
                    // simplified result so that identical unsimplified
                    // sub-expressions elsewhere in the tree get a cache hit.
                    if state.expr.hash() != annotated.hash() {
                        let ctx = state.expr.context();
                        let hash = state.expr.hash();
                        let annotated_ref = annotated.clone();
                        let _ = ctx
                            .simplification_cache
                            .get_or_insert::<SimplifyError<'c>>(hash, || Ok(annotated_ref.clone()));
                    }

                    last_result = Some(annotated)
                }
                Err(SimplifyError::MissingChild(index)) => {
                    let child_state = SimplifyState::new(state.expr.get_child(index).unwrap());

                    // Push the current state back onto the stack
                    work_stack.push(state);
                    // Push the missing child onto the stack
                    work_stack.push(child_state);
                }
                Err(SimplifyError::MissingChildren(indices)) => {
                    // Batch-simplify all missing children at once to avoid
                    // O(n^2) behaviour for wide n-ary ops like Concat. We use
                    // direct recursion here: the parent op is allowed to
                    // defer all its children with a single request and we
                    // simplify each child via the normal entry point. Stack
                    // depth is bounded by the nesting depth of n-ary ops,
                    // not by the number of children.
                    for idx in indices {
                        if state.children[idx].is_none() {
                            let child_expr = state.expr.get_child(idx).unwrap();
                            let simplified =
                                simplify(&child_expr, respect_annotations, error_on_dbz)?;
                            state.children[idx] = Some(simplified);
                        }
                    }
                    // All requested children are now cached; re-push the
                    // state so simplify_inner will run again with children
                    // available.
                    work_stack.push(state);
                }
                Err(SimplifyError::ReRun(new_ast)) => {
                    // Forward the rewritten node's relocatable annotations onto the
                    // rewritten expression so they are not dropped across the rerun.
                    let relocatable_annotations: Vec<Annotation> = state
                        .expr
                        .annotations()
                        .iter()
                        .filter(|a| a.relocatable())
                        .cloned()
                        .collect();
                    let new_ast = if relocatable_annotations.is_empty() {
                        new_ast
                    } else {
                        state
                            .expr
                            .context()
                            .annotate(&new_ast, relocatable_annotations)?
                    };
                    // Push a new state with the new_ast onto the stack
                    work_stack.push(SimplifyState::new(new_ast));
                }
                Err(SimplifyError::Error(e)) => {
                    return Err(e);
                }
            }
        } else {
            last_result = Some(state.expr.clone());
        }
    }

    if last_result.is_none() {
        return Err(ClarirsError::InvalidArguments(
            "No result produced".to_string(),
        ));
    }

    Ok(last_result.unwrap())
}

fn simplify_bool<'c>(state: &mut SimplifyState<'c>) -> Result<AstRef<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let bool_ast = state.expr.clone();

    match bool_ast.op() {
        AstOp::BoolS(_) | AstOp::BoolV(_) => Ok(bool_ast),
        AstOp::Not(..) => {
            let arc = state.get_child_simplified(0)?;

            match arc.op() {
                AstOp::Not(arc) => Ok(arc.clone()),
                AstOp::BoolV(v) => Ok(ctx.boolv(!v)?),

                AstOp::Eq(lhs, rhs) => Ok(ctx.neq(lhs.clone(), rhs.clone())?),
                AstOp::Neq(lhs, rhs) => Ok(ctx.eq_(lhs.clone(), rhs.clone())?),

                // !(a > b)  ==>  a <= b
                AstOp::UGT(lhs, rhs) => state.rerun(ctx.ule(lhs.clone(), rhs.clone())?),
                // !(a >= b)  ==>  a < b
                AstOp::UGE(lhs, rhs) => state.rerun(ctx.ult(lhs.clone(), rhs.clone())?),
                // !(a < b)  ==>  a >= b
                AstOp::ULT(lhs, rhs) => state.rerun(ctx.uge(lhs.clone(), rhs.clone())?),
                // !(a <= b)  ==>  a > b
                AstOp::ULE(lhs, rhs) => state.rerun(ctx.ugt(lhs.clone(), rhs.clone())?),
                // !(a s> b)  ==>  a s<= b
                AstOp::SGT(lhs, rhs) => state.rerun(ctx.sle(lhs.clone(), rhs.clone())?),
                // !(a s>= b)  ==>  a s< b
                AstOp::SGE(lhs, rhs) => state.rerun(ctx.slt(lhs.clone(), rhs.clone())?),
                // !(a s< b)  ==>  a s>= b
                AstOp::SLT(lhs, rhs) => state.rerun(ctx.sge(lhs.clone(), rhs.clone())?),
                // !(a s<= b)  ==>  a s> b
                AstOp::SLE(lhs, rhs) => state.rerun(ctx.sgt(lhs.clone(), rhs.clone())?),

                _ => Ok(ctx.not(arc)?),
            }
        }
        AstOp::And(args) => {
            let available_args = (0..args.len())
                .map(|i| state.get_child_available(i))
                .collect::<Vec<_>>();

            // Absorption simplification
            let absorbed_args = available_args
                .into_iter()
                .flat_map(|arg| {
                    if let AstOp::And(nested_args) = arg.op() {
                        nested_args.clone()
                    } else {
                        vec![arg]
                    }
                })
                .filter(|arg| !matches!(arg.op(), AstOp::BoolV(true)))
                .collect::<Vec<_>>();
            // Deduplicate using == comparison
            let mut deduped = Vec::with_capacity(absorbed_args.len());
            for arg in absorbed_args {
                if !deduped.iter().any(|existing| existing == &arg) {
                    deduped.push(arg);
                }
            }
            let absorbed_args = deduped;

            if absorbed_args.is_empty() {
                return Ok(ctx.true_()?);
            }
            if absorbed_args.len() == 1 {
                return state.rerun(absorbed_args[0].clone());
            }

            // Identity simplification
            if absorbed_args
                .iter()
                .any(|arg| matches!(arg.op(), AstOp::BoolV(false)))
            {
                return Ok(ctx.false_()?);
            }

            // x & !x == false
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    if let AstOp::Not(neg) = absorbed_args[i].op()
                        && neg == &absorbed_args[j]
                    {
                        return Ok(ctx.false_()?);
                    }
                    if let AstOp::Not(neg) = absorbed_args[j].op()
                        && neg == &absorbed_args[i]
                    {
                        return Ok(ctx.false_()?);
                    }
                }
            }

            // All of the comparisons
            // ex x == K & x != K  ==>  false
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    match (absorbed_args[i].op(), absorbed_args[j].op()) {
                        (AstOp::Eq(var1, val1), AstOp::Neq(var2, val2))
                        | (AstOp::Neq(var2, val2), AstOp::Eq(var1, val1))
                        | (AstOp::ULT(var1, val1), AstOp::UGE(var2, val2))
                        | (AstOp::UGE(var2, val2), AstOp::ULT(var1, val1))
                        | (AstOp::ULE(var1, val1), AstOp::UGT(var2, val2))
                        | (AstOp::UGT(var2, val2), AstOp::ULE(var1, val1))
                        | (AstOp::SLT(var1, val1), AstOp::SGE(var2, val2))
                        | (AstOp::SGE(var2, val2), AstOp::SLT(var1, val1))
                        | (AstOp::SLE(var1, val1), AstOp::SGT(var2, val2))
                        | (AstOp::SGT(var2, val2), AstOp::SLE(var1, val1))
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

            // Simplify all children in one batch to avoid quadratic re-runs
            // for wide And.
            let simplified_args = state.get_all_simplified()?;
            Ok(ctx.and(simplified_args)?)
        }
        AstOp::Or(args) => {
            let available_args = (0..args.len())
                .map(|i| state.get_child_available(i))
                .collect::<Vec<_>>();

            // Absorption simplification
            let absorbed_args = available_args
                .into_iter()
                .flat_map(|arg| {
                    if let AstOp::Or(nested_args) = arg.op() {
                        nested_args.clone()
                    } else {
                        vec![arg]
                    }
                })
                .filter(|arg| !matches!(arg.op(), AstOp::BoolV(false)))
                .collect::<Vec<_>>();
            // Deduplicate using == comparison
            let mut deduped = Vec::with_capacity(absorbed_args.len());
            for arg in absorbed_args {
                if !deduped.iter().any(|existing| existing == &arg) {
                    deduped.push(arg);
                }
            }
            let absorbed_args = deduped;

            // Identity simplification
            if absorbed_args
                .iter()
                .any(|arg| matches!(arg.op(), AstOp::BoolV(true)))
            {
                return Ok(ctx.true_()?);
            }

            if absorbed_args.is_empty() {
                return Ok(ctx.false_()?);
            }
            if absorbed_args.len() == 1 {
                return state.rerun(absorbed_args[0].clone());
            }

            // x | !x == true
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    if let AstOp::Not(neg) = absorbed_args[i].op()
                        && neg == &absorbed_args[j]
                    {
                        return Ok(ctx.true_()?);
                    }
                    if let AstOp::Not(neg) = absorbed_args[j].op()
                        && neg == &absorbed_args[i]
                    {
                        return Ok(ctx.true_()?);
                    }
                }
            }

            // All of the comparisons
            // ex x == K | x != K  ==>  true
            for i in 0..absorbed_args.len() {
                for j in (i + 1)..absorbed_args.len() {
                    match (absorbed_args[i].op(), absorbed_args[j].op()) {
                        (AstOp::Eq(var1, val1), AstOp::Neq(var2, val2))
                        | (AstOp::Neq(var2, val2), AstOp::Eq(var1, val1))
                        | (AstOp::ULT(var1, val1), AstOp::UGE(var2, val2))
                        | (AstOp::UGE(var2, val2), AstOp::ULT(var1, val1))
                        | (AstOp::ULE(var1, val1), AstOp::UGT(var2, val2))
                        | (AstOp::UGT(var2, val2), AstOp::ULE(var1, val1))
                        | (AstOp::SLT(var1, val1), AstOp::SGE(var2, val2))
                        | (AstOp::SGE(var2, val2), AstOp::SLT(var1, val1))
                        | (AstOp::SLE(var1, val1), AstOp::SGT(var2, val2))
                        | (AstOp::SGT(var2, val2), AstOp::SLE(var1, val1))
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

            // Simplify all children in one batch to avoid quadratic re-runs
            // for wide Or.
            let simplified_args = state.get_all_simplified()?;
            Ok(ctx.or(simplified_args)?)
        }
        AstOp::Xor(..) => {
            // n-ary boolean xor: fold constants into a parity bit, strip
            // negations (Not(x) = x ^ true), and cancel repeated operands in
            // pairs (x ^ x = false).
            let args = state.get_all_simplified()?;
            let mut parity = false;
            let mut operands: Vec<AstRef> = Vec::with_capacity(args.len());
            for arg in args {
                match arg.op() {
                    AstOp::BoolV(b) => parity ^= b,
                    AstOp::Not(inner) => {
                        parity = !parity;
                        operands.push(inner.clone());
                    }
                    _ => operands.push(arg),
                }
            }

            // xor of k copies of x is x when k is odd, false when k is even
            let mut counts: HashMap<u64, usize> = HashMap::new();
            for o in &operands {
                *counts.entry(o.hash()).or_default() += 1;
            }
            let mut seen = HashSet::new();
            let rest: Vec<_> = operands
                .into_iter()
                .filter(|o| counts[&o.hash()] % 2 == 1 && seen.insert(o.hash()))
                .collect();

            let combined = match rest.len() {
                0 => ctx.boolv(false)?,
                1 => rest[0].clone(),
                _ => ctx.xor(rest)?,
            };
            if parity {
                match combined.op() {
                    AstOp::BoolV(b) => Ok(ctx.boolv(!b)?),
                    // Re-simplify the produced negation so Not(comparison) ->
                    // inverse-comparison rules apply, matching a directly-built Not.
                    _ => state.rerun(ctx.not(combined)?),
                }
            } else {
                Ok(combined)
            }
        }
        AstOp::Eq(..) => match state.get_child_available(0).ast_type() {
            AstType::Bool => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::BoolV(arc), AstOp::BoolV(arc1)) => Ok(ctx.boolv(arc == arc1)?),
                    (AstOp::BoolV(true), _) => Ok(state.get_child_simplified(1)?),
                    (_, AstOp::BoolV(true)) => Ok(state.get_child_simplified(0)?),
                    // x == false -> !x; rerun so the produced Not canonicalizes.
                    (AstOp::BoolV(false), _) => state.rerun(ctx.not(&early_rhs)?),
                    (_, AstOp::BoolV(false)) => state.rerun(ctx.not(&early_lhs)?),
                    // a == a -> true. Even when floats are involved, this is a boolean
                    // identity: both sides are the same expression and evaluate to the same
                    // value (NaN only affects fp== itself, not bool== of two equal booleans).
                    _ if early_lhs == early_rhs => Ok(ctx.true_()?),
                    _ => Ok(ctx.eq_(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
            AstType::Float(_) => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::FPV(arc), AstOp::FPV(arc1)) => Ok(ctx.boolv(arc.compare_fp(arc1))?),
                    _ => Ok(ctx.fp_eq(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
            AstType::String => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::StringV(str1), AstOp::StringV(str2)) => Ok(ctx.boolv(str1 == str2)?),
                    _ => Ok(ctx.str_eq(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
            AstType::BitVec(_) => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                    (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc == arc1)?),

                    // If on one side there is an AND where one of the operands is a mask, and on the
                    // other side, there is a BVV which matches the masked part of the AND, we can
                    // extract the AND operand directly, and extract the other side and rerun
                    (AstOp::And(and_args), AstOp::BVV(bvv))
                        if and_args
                            .iter()
                            .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                    {
                        let mask_idx = and_args
                            .iter()
                            .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                            .unwrap();
                        let mask = &and_args[mask_idx];
                        let remaining: Vec<_> = and_args
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != mask_idx)
                            .map(|(_, a)| a.clone())
                            .collect();
                        let lhs_and = if remaining.len() == 1 {
                            remaining.into_iter().next().unwrap()
                        } else {
                            ctx.and(remaining)?
                        };
                        let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask()
                        } else {
                            None
                        }
                        .expect("Checked above, switch to if let when stabilized");
                        state.rerun(ctx.eq_(
                            ctx.extract(&lhs_and, mask_high, mask_low)?,
                            ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        )?)
                    }

                    // If one side is a = ZeroExt and the other side is a BVV with those bits set to zero,
                    // we can extract the relevant bits and compare directly
                    (AstOp::ZeroExt(innner, ext_size), AstOp::BVV(outer))
                    | (AstOp::BVV(outer), AstOp::ZeroExt(innner, ext_size))
                        if outer.leading_zeros() as u32 >= *ext_size =>
                    {
                        state.rerun(ctx.eq_(
                            innner.clone(),
                            ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        )?)
                    }

                    // If both sides are ZeroExt of the same size, we can compare the inner values directly
                    (AstOp::ZeroExt(inner_lhs, _), AstOp::ZeroExt(inner_rhs, _)) => {
                        state.rerun(ctx.eq_(inner_lhs.clone(), inner_rhs.clone())?)
                    }

                    // (ite cond 1 0) == 0  ==>  !cond
                    (AstOp::ITE(cond, then_val, else_val), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::ITE(cond, then_val, else_val))
                        if val.is_zero() =>
                    {
                        if let (AstOp::BVV(then_bvv), AstOp::BVV(else_bvv)) =
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
                        Ok(ctx.eq_(
                            state.get_child_simplified(0)?,
                            state.get_child_simplified(1)?,
                        )?)
                    }

                    // (ite cond 1 0) == 1  ==>  cond
                    (AstOp::ITE(cond, then_val, else_val), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::ITE(cond, then_val, else_val))
                        if val.is_one() =>
                    {
                        if let (AstOp::BVV(then_bvv), AstOp::BVV(else_bvv)) =
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
                        Ok(ctx.eq_(
                            state.get_child_simplified(0)?,
                            state.get_child_simplified(1)?,
                        )?)
                    }

                    // (x - C) == 0  ==>  x == C
                    (AstOp::Sub(lhs_sub, rhs_sub), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::Sub(lhs_sub, rhs_sub))
                        if val.is_zero() && matches!(rhs_sub.op(), AstOp::BVV(..)) =>
                    {
                        state.rerun(ctx.eq_(lhs_sub.clone(), rhs_sub.clone())?)
                    }

                    // (sum + C) == 0  ==>  sum == -C
                    (AstOp::Add(add_args), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::Add(add_args))
                        if val.is_zero()
                            && add_args.iter().any(|a| matches!(a.op(), AstOp::BVV(..))) =>
                    {
                        if let Some(bvv_idx) = add_args
                            .iter()
                            .position(|a| matches!(a.op(), AstOp::BVV(..)))
                        {
                            let neg_c = ctx.neg(&add_args[bvv_idx])?;
                            let remaining: Vec<_> = add_args
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != bvv_idx)
                                .map(|(_, a)| a.clone())
                                .collect();
                            let lhs = if remaining.len() == 1 {
                                remaining.into_iter().next().unwrap()
                            } else {
                                ctx.add_many(remaining)?
                            };
                            state.rerun(ctx.eq_(lhs, neg_c)?)
                        } else {
                            unreachable!()
                        }
                    }

                    _ => Ok(ctx.eq_(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
        },
        AstOp::Neq(..) => match state.get_child_available(0).ast_type() {
            AstType::Bool => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::BoolV(arc), AstOp::BoolV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                    // x != true -> !x; rerun so the produced Not canonicalizes.
                    (AstOp::BoolV(true), _) => state.rerun(ctx.not(&early_rhs)?),
                    (_, AstOp::BoolV(true)) => state.rerun(ctx.not(&early_lhs)?),
                    (AstOp::BoolV(false), _) => Ok(state.get_child_simplified(1)?),
                    (_, AstOp::BoolV(false)) => Ok(state.get_child_simplified(0)?),
                    // a != a -> false. Even when floats are involved, this is a boolean
                    // identity: both sides are the same expression and evaluate to the same
                    // value (NaN only affects fp!= itself, not bool!= of two equal booleans).
                    _ if early_lhs == early_rhs => Ok(ctx.false_()?),
                    _ => Ok(ctx.neq(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
            AstType::Float(_) => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::FPV(arc), AstOp::FPV(arc1)) => Ok(ctx.boolv(!arc.compare_fp(arc1))?),
                    _ => Ok(ctx.fp_neq(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
            AstType::String => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::StringV(str1), AstOp::StringV(str2)) => Ok(ctx.boolv(str1 != str2)?),
                    _ => Ok(ctx.str_neq(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
            AstType::BitVec(_) => {
                let early_lhs = state.get_child_available(0);
                let early_rhs = state.get_child_available(1);

                match (early_lhs.op(), early_rhs.op()) {
                    (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                    (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),

                    // If on one side there is an AND where one of the operands is a mask, and on the
                    // other side, there is a BVV which matches the masked part of the AND, we can
                    // extract the AND operand directly, and extract the other side and rerun
                    (AstOp::And(and_args), AstOp::BVV(bvv))
                        if and_args
                            .iter()
                            .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                    {
                        let mask_idx = and_args
                            .iter()
                            .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                            .unwrap();
                        let mask = &and_args[mask_idx];
                        let remaining: Vec<_> = and_args
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != mask_idx)
                            .map(|(_, a)| a.clone())
                            .collect();
                        let lhs_and = if remaining.len() == 1 {
                            remaining.into_iter().next().unwrap()
                        } else {
                            ctx.and(remaining)?
                        };
                        let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                            mask_val.is_mask()
                        } else {
                            None
                        }
                        .expect("Checked above, switch to if let when stabilized");
                        state.rerun(ctx.neq(
                            ctx.extract(&lhs_and, mask_high, mask_low)?,
                            ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        )?)
                    }

                    // If one side is a = ZeroExt and the other side is a BVV with those bits set to zero,
                    // we can extract the relevant bits and compare directly
                    (AstOp::ZeroExt(innner, ext_size), AstOp::BVV(outer))
                    | (AstOp::BVV(outer), AstOp::ZeroExt(innner, ext_size))
                        if outer.leading_zeros() as u32 >= *ext_size =>
                    {
                        state.rerun(ctx.neq(
                            innner.clone(),
                            ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        )?)
                    }

                    // If both sides are ZeroExt of the same size, we can compare the inner values directly
                    (AstOp::ZeroExt(inner_lhs, _), AstOp::ZeroExt(inner_rhs, _)) => {
                        state.rerun(ctx.neq(inner_lhs.clone(), inner_rhs.clone())?)
                    }

                    // (ite cond 1 0) != 0  ==>  cond
                    (AstOp::ITE(cond, then_val, else_val), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::ITE(cond, then_val, else_val))
                        if val.is_zero() =>
                    {
                        if let (AstOp::BVV(then_bvv), AstOp::BVV(else_bvv)) =
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
                        Ok(ctx.neq(
                            state.get_child_simplified(0)?,
                            state.get_child_simplified(1)?,
                        )?)
                    }

                    // (ite cond 1 0) != 1  ==>  !cond
                    (AstOp::ITE(cond, then_val, else_val), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::ITE(cond, then_val, else_val))
                        if val.is_one() =>
                    {
                        if let (AstOp::BVV(then_bvv), AstOp::BVV(else_bvv)) =
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
                        Ok(ctx.neq(
                            state.get_child_simplified(0)?,
                            state.get_child_simplified(1)?,
                        )?)
                    }

                    // (x - C) != 0  ==>  x != C
                    (AstOp::Sub(lhs_sub, rhs_sub), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::Sub(lhs_sub, rhs_sub))
                        if val.is_zero() && matches!(rhs_sub.op(), AstOp::BVV(..)) =>
                    {
                        state.rerun(ctx.neq(lhs_sub.clone(), rhs_sub.clone())?)
                    }

                    // (sum + C) != 0  ==>  sum != -C
                    (AstOp::Add(add_args), AstOp::BVV(val))
                    | (AstOp::BVV(val), AstOp::Add(add_args))
                        if val.is_zero()
                            && add_args.iter().any(|a| matches!(a.op(), AstOp::BVV(..))) =>
                    {
                        if let Some(bvv_idx) = add_args
                            .iter()
                            .position(|a| matches!(a.op(), AstOp::BVV(..)))
                        {
                            let neg_c = ctx.neg(&add_args[bvv_idx])?;
                            let remaining: Vec<_> = add_args
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != bvv_idx)
                                .map(|(_, a)| a.clone())
                                .collect();
                            let lhs = if remaining.len() == 1 {
                                remaining.into_iter().next().unwrap()
                            } else {
                                ctx.add_many(remaining)?
                            };
                            state.rerun(ctx.neq(lhs, neg_c)?)
                        } else {
                            unreachable!()
                        }
                    }

                    _ => Ok(ctx.neq(
                        state.get_child_simplified(0)?,
                        state.get_child_simplified(1)?,
                    )?),
                }
            }
        },
        AstOp::ULT(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc < arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (AstOp::And(and_args), AstOp::BVV(bvv))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ult(
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (AstOp::BVV(bvv), AstOp::And(and_args))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ult(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (AstOp::ZeroExt(innner, ext_size), AstOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ult(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (AstOp::BVV(outer), AstOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ult(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (AstOp::ZeroExt(inner_lhs, _), AstOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.ult(inner_lhs.clone(), inner_rhs.clone())?)
                }

                // ULT(Concat(rest..., BVV(0, n)), BVV(c)) where c has n trailing zeros
                (AstOp::Concat(args), AstOp::BVV(c_val)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.ult(
                            high_part,
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                        )?)
                    } else {
                        Ok(ctx.ult(arc, arc1)?)
                    }
                }
                (AstOp::BVV(c_val), AstOp::Concat(args)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.ult(
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                            high_part,
                        )?)
                    } else {
                        Ok(ctx.ult(arc, arc1)?)
                    }
                }

                // ULT(BVV(b), Sub(ZeroExt(n, inner), BVV(c))) where c and b fit in inner's size
                // => ULT(extract(b), Sub(inner, extract(c)))
                (AstOp::BVV(bound), AstOp::Sub(lhs_sub, rhs_sub))
                    if matches!(lhs_sub.op(), AstOp::ZeroExt(_, ext_size)
                        if bound.leading_zeros() as u32 >= *ext_size
                        && matches!(rhs_sub.op(), AstOp::BVV(c) if c.leading_zeros() as u32 >= *ext_size)) =>
                {
                    if let AstOp::ZeroExt(inner, _) = lhs_sub.op() {
                        let inner_size = inner.size();
                        state.rerun(ctx.ult(
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                            ctx.sub(inner, &ctx.extract(rhs_sub, inner_size - 1, 0)?)?,
                        )?)
                    } else {
                        unreachable!()
                    }
                }

                // ULT(Sub(ZeroExt(n, inner), BVV(c)), BVV(b)) where c and b fit in inner's size
                // => ULT(Sub(inner, extract(c)), extract(b))
                (AstOp::Sub(lhs_sub, rhs_sub), AstOp::BVV(bound))
                    if matches!(lhs_sub.op(), AstOp::ZeroExt(_, ext_size)
                        if bound.leading_zeros() as u32 >= *ext_size
                        && matches!(rhs_sub.op(), AstOp::BVV(c) if c.leading_zeros() as u32 >= *ext_size)) =>
                {
                    if let AstOp::ZeroExt(inner, _) = lhs_sub.op() {
                        let inner_size = inner.size();
                        state.rerun(ctx.ult(
                            ctx.sub(inner, &ctx.extract(rhs_sub, inner_size - 1, 0)?)?,
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                        )?)
                    } else {
                        unreachable!()
                    }
                }

                // ULT(BVV(b), Add(ZeroExt(n, inner), BVV(c))) where c and b fit in inner's size
                (AstOp::BVV(bound), AstOp::Add(add_args)) => {
                    let ze_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::ZeroExt(..)));
                    let bvv_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(..)));
                    if let (Some(ze_i), Some(bvv_i)) = (ze_idx, bvv_idx)
                        && ze_i != bvv_i
                        && add_args.len() == 2
                        && let AstOp::ZeroExt(inner, ext_size) = add_args[ze_i].op()
                        && let AstOp::BVV(c) = add_args[bvv_i].op()
                        && bound.leading_zeros() as u32 >= *ext_size
                        && c.leading_zeros() as u32 >= *ext_size
                    {
                        let inner_size = inner.size();
                        return state.rerun(ctx.ult(
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                            ctx.add(inner, &ctx.extract(&add_args[bvv_i], inner_size - 1, 0)?)?,
                        )?);
                    }
                    Ok(ctx.ult(arc, arc1)?)
                }

                _ => Ok(ctx.ult(arc, arc1)?),
            }
        }
        AstOp::ULE(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc <= arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (AstOp::And(and_args), AstOp::BVV(bvv))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ule(
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (AstOp::BVV(bvv), AstOp::And(and_args))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ule(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a ZeroExt, and the other side is a BVV with a value larger than
                // what can be represented in the inner bits, we can concretize the comparison
                (AstOp::ZeroExt(inner, _), AstOp::BVV(outer))
                    if outer.bits() > inner.size() as usize =>
                {
                    Ok(ctx.true_()?)
                }
                (AstOp::BVV(outer), AstOp::ZeroExt(inner, _))
                    if outer.bits() > inner.size() as usize =>
                {
                    Ok(ctx.false_()?)
                }

                // If one side is a ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (AstOp::ZeroExt(innner, ext_size), AstOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ule(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (AstOp::BVV(outer), AstOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ule(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (AstOp::ZeroExt(inner_lhs, _), AstOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.ule(inner_lhs.clone(), inner_rhs.clone())?)
                }

                // ULE(Sub(ZeroExt(n, inner), BVV(c)), BVV(b)) where c and b fit in inner's size
                // => ULE(Sub(inner, extract(c)), extract(b))
                (AstOp::Sub(lhs_sub, rhs_sub), AstOp::BVV(bound))
                    if matches!(lhs_sub.op(), AstOp::ZeroExt(_, ext_size)
                        if bound.leading_zeros() as u32 >= *ext_size
                        && matches!(rhs_sub.op(), AstOp::BVV(c) if c.leading_zeros() as u32 >= *ext_size)) =>
                {
                    if let AstOp::ZeroExt(inner, _) = lhs_sub.op() {
                        let inner_size = inner.size();
                        state.rerun(ctx.ule(
                            ctx.sub(inner, &ctx.extract(rhs_sub, inner_size - 1, 0)?)?,
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                        )?)
                    } else {
                        unreachable!()
                    }
                }

                // ULE(Add(ZeroExt(n, inner), BVV(c)), BVV(b)) where c and b fit in inner's size
                (AstOp::Add(add_args), AstOp::BVV(bound)) => {
                    let ze_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::ZeroExt(..)));
                    let bvv_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(..)));
                    if let (Some(ze_i), Some(bvv_i)) = (ze_idx, bvv_idx)
                        && ze_i != bvv_i
                        && add_args.len() == 2
                        && let AstOp::ZeroExt(inner, ext_size) = add_args[ze_i].op()
                        && let AstOp::BVV(c) = add_args[bvv_i].op()
                        && bound.leading_zeros() as u32 >= *ext_size
                        && c.leading_zeros() as u32 >= *ext_size
                    {
                        let inner_size = inner.size();
                        return state.rerun(ctx.ule(
                            ctx.add(inner, &ctx.extract(&add_args[bvv_i], inner_size - 1, 0)?)?,
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                        )?);
                    }
                    Ok(ctx.ule(arc, arc1)?)
                }

                // ULE(Concat(rest..., BVV(0, n)), BVV(c)) where c has n trailing zeros
                (AstOp::Concat(args), AstOp::BVV(c_val)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.ule(
                            high_part,
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                        )?)
                    } else {
                        Ok(ctx.ule(arc, arc1)?)
                    }
                }
                (AstOp::BVV(c_val), AstOp::Concat(args)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.ule(
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                            high_part,
                        )?)
                    } else {
                        Ok(ctx.ule(arc, arc1)?)
                    }
                }

                _ => Ok(ctx.ule(arc, arc1)?),
            }
        }
        AstOp::UGT(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc > arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (AstOp::And(and_args), AstOp::BVV(bvv))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ugt(
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (AstOp::BVV(bvv), AstOp::And(and_args))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.ugt(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a ZeroExt, and the other side is a BVV with a value larger than
                // what can be represented in the inner bits, we can concretize the comparison
                (AstOp::ZeroExt(inner, _), AstOp::BVV(outer))
                    if outer.bits() > inner.size() as usize =>
                {
                    Ok(ctx.false_()?)
                }
                (AstOp::BVV(outer), AstOp::ZeroExt(inner, _))
                    if outer.bits() > inner.size() as usize =>
                {
                    Ok(ctx.true_()?)
                }

                // If one side is a ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (AstOp::ZeroExt(innner, ext_size), AstOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ugt(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (AstOp::BVV(outer), AstOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.ugt(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (AstOp::ZeroExt(inner_lhs, _), AstOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.ugt(inner_lhs.clone(), inner_rhs.clone())?)
                }

                // UGT(Sub(ZeroExt(n, inner), BVV(c)), BVV(b)) where c and b fit in inner's size
                (AstOp::Sub(lhs_sub, rhs_sub), AstOp::BVV(bound))
                    if matches!(lhs_sub.op(), AstOp::ZeroExt(_, ext_size)
                        if bound.leading_zeros() as u32 >= *ext_size
                        && matches!(rhs_sub.op(), AstOp::BVV(c) if c.leading_zeros() as u32 >= *ext_size)) =>
                {
                    if let AstOp::ZeroExt(inner, _) = lhs_sub.op() {
                        let inner_size = inner.size();
                        state.rerun(ctx.ugt(
                            ctx.sub(inner, &ctx.extract(rhs_sub, inner_size - 1, 0)?)?,
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                        )?)
                    } else {
                        unreachable!()
                    }
                }

                // UGT(Add(ZeroExt(n, inner), BVV(c)), BVV(b)) where c and b fit in inner's size
                (AstOp::Add(add_args), AstOp::BVV(bound)) => {
                    let ze_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::ZeroExt(..)));
                    let bvv_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(..)));
                    if let (Some(ze_i), Some(bvv_i)) = (ze_idx, bvv_idx)
                        && ze_i != bvv_i
                        && add_args.len() == 2
                        && let AstOp::ZeroExt(inner, ext_size) = add_args[ze_i].op()
                        && let AstOp::BVV(c) = add_args[bvv_i].op()
                        && bound.leading_zeros() as u32 >= *ext_size
                        && c.leading_zeros() as u32 >= *ext_size
                    {
                        let inner_size = inner.size();
                        return state.rerun(ctx.ugt(
                            ctx.add(inner, &ctx.extract(&add_args[bvv_i], inner_size - 1, 0)?)?,
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                        )?);
                    }
                    Ok(ctx.ugt(arc, arc1)?)
                }

                // UGT(Concat(rest..., BVV(0, n)), BVV(c)) where c has n trailing zeros
                (AstOp::Concat(args), AstOp::BVV(c_val)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.ugt(
                            high_part,
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                        )?)
                    } else {
                        Ok(ctx.ugt(arc, arc1)?)
                    }
                }
                (AstOp::BVV(c_val), AstOp::Concat(args)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.ugt(
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                            high_part,
                        )?)
                    } else {
                        Ok(ctx.ugt(arc, arc1)?)
                    }
                }

                _ => Ok(ctx.ugt(arc, arc1)?),
            }
        }
        AstOp::UGE(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc >= arc1)?),

                // If on one side there is an AND where one of the operands is a mask, and on the
                // other side, there is a BVV which matches the masked part of the AND, we can
                // extract the AND operand directly, and extract the other side and rerun
                (AstOp::And(and_args), AstOp::BVV(bvv))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.uge(
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                    )?)
                }
                (AstOp::BVV(bvv), AstOp::And(and_args))
                    if and_args
                        .iter()
                        .any(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some())) =>
                {
                    let mask_idx = and_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(v) if v.is_mask().is_some()))
                        .unwrap();
                    let mask = &and_args[mask_idx];
                    let remaining: Vec<_> = and_args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != mask_idx)
                        .map(|(_, a)| a.clone())
                        .collect();
                    let lhs_and = if remaining.len() == 1 {
                        remaining.into_iter().next().unwrap()
                    } else {
                        ctx.and(remaining)?
                    };
                    let (mask_high, mask_low) = if let AstOp::BVV(mask_val) = mask.op() {
                        mask_val.is_mask()
                    } else {
                        None
                    }
                    .expect("Checked above, switch to if let when stabilized");
                    state.rerun(ctx.uge(
                        ctx.bvv(bvv.extract(mask_low, mask_high)?)?,
                        ctx.extract(&lhs_and, mask_high, mask_low)?,
                    )?)
                }

                // If one side is a ZeroExt and the other side is a BVV with those bits set to zero,
                // we can extract the relevant bits and compare directly
                (AstOp::ZeroExt(innner, ext_size), AstOp::BVV(outer))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.uge(
                        innner.clone(),
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                    )?)
                }
                (AstOp::BVV(outer), AstOp::ZeroExt(innner, ext_size))
                    if outer.leading_zeros() as u32 >= *ext_size =>
                {
                    state.rerun(ctx.uge(
                        ctx.extract(ctx.bvv(outer.clone())?, innner.size() - 1, 0)?,
                        innner.clone(),
                    )?)
                }

                // If both sides are ZeroExt of the same size, we can compare the inner values directly
                (AstOp::ZeroExt(inner_lhs, _), AstOp::ZeroExt(inner_rhs, _)) => {
                    state.rerun(ctx.uge(inner_lhs.clone(), inner_rhs.clone())?)
                }

                // UGE(Concat(rest..., BVV(0, n)), BVV(c)) where c has n trailing zeros
                (AstOp::Concat(args), AstOp::BVV(c_val)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.uge(
                            high_part,
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                        )?)
                    } else {
                        Ok(ctx.uge(arc, arc1)?)
                    }
                }
                (AstOp::BVV(c_val), AstOp::Concat(args)) if matches!(args.last().map(|a| a.op()), Some(AstOp::BVV(v)) if v.is_zero()) =>
                {
                    let low_bits = args.last().unwrap().size();
                    if c_val
                        .extract(0, low_bits - 1)
                        .map(|v| v.is_zero())
                        .unwrap_or(false)
                    {
                        let high_parts: Vec<_> = args[..args.len() - 1].to_vec();
                        let high_part = if high_parts.len() == 1 {
                            high_parts.into_iter().next().unwrap()
                        } else {
                            ctx.concat(high_parts)?
                        };
                        state.rerun(ctx.uge(
                            ctx.bvv(c_val.extract(low_bits, c_val.len() - 1)?)?,
                            high_part,
                        )?)
                    } else {
                        Ok(ctx.uge(arc, arc1)?)
                    }
                }

                // UGE(BVV(b), Sub(ZeroExt(n, inner), BVV(c))) where c and b fit in inner's size
                // => UGE(extract(b), Sub(inner, extract(c)))
                (AstOp::BVV(bound), AstOp::Sub(lhs_sub, rhs_sub))
                    if matches!(lhs_sub.op(), AstOp::ZeroExt(_, ext_size)
                        if bound.leading_zeros() as u32 >= *ext_size
                        && matches!(rhs_sub.op(), AstOp::BVV(c) if c.leading_zeros() as u32 >= *ext_size)) =>
                {
                    if let AstOp::ZeroExt(inner, _) = lhs_sub.op() {
                        let inner_size = inner.size();
                        state.rerun(ctx.uge(
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                            ctx.sub(inner, &ctx.extract(rhs_sub, inner_size - 1, 0)?)?,
                        )?)
                    } else {
                        unreachable!()
                    }
                }

                // UGE(Sub(ZeroExt(n, inner), BVV(c)), BVV(b)) where c and b fit in inner's size
                // => UGE(Sub(inner, extract(c)), extract(b))
                (AstOp::Sub(lhs_sub, rhs_sub), AstOp::BVV(bound))
                    if matches!(lhs_sub.op(), AstOp::ZeroExt(_, ext_size)
                        if bound.leading_zeros() as u32 >= *ext_size
                        && matches!(rhs_sub.op(), AstOp::BVV(c) if c.leading_zeros() as u32 >= *ext_size)) =>
                {
                    if let AstOp::ZeroExt(inner, _) = lhs_sub.op() {
                        let inner_size = inner.size();
                        state.rerun(ctx.uge(
                            ctx.sub(inner, &ctx.extract(rhs_sub, inner_size - 1, 0)?)?,
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                        )?)
                    } else {
                        unreachable!()
                    }
                }

                // UGE(BVV(b), Add(ZeroExt(n, inner), BVV(c))) where c and b fit in inner's size
                (AstOp::BVV(bound), AstOp::Add(add_args)) => {
                    let ze_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::ZeroExt(..)));
                    let bvv_idx = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(..)));
                    if let (Some(ze_i), Some(bvv_i)) = (ze_idx, bvv_idx)
                        && ze_i != bvv_i
                        && add_args.len() == 2
                        && let AstOp::ZeroExt(inner, ext_size) = add_args[ze_i].op()
                        && let AstOp::BVV(c) = add_args[bvv_i].op()
                        && bound.leading_zeros() as u32 >= *ext_size
                        && c.leading_zeros() as u32 >= *ext_size
                    {
                        let inner_size = inner.size();
                        return state.rerun(ctx.uge(
                            ctx.bvv(bound.extract(0, inner_size - 1)?)?,
                            ctx.add(inner, &ctx.extract(&add_args[bvv_i], inner_size - 1, 0)?)?,
                        )?);
                    }
                    Ok(ctx.uge(arc, arc1)?)
                }

                _ => Ok(ctx.uge(arc, arc1)?),
            }
        }
        AstOp::SLT(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_lt(arc1))?),
                _ => Ok(ctx.slt(arc, arc1)?),
            }
        }
        AstOp::SLE(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_le(arc1))?),
                _ => Ok(ctx.sle(arc, arc1)?),
            }
        }
        AstOp::SGT(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_gt(arc1))?),
                _ => Ok(ctx.sgt(arc, arc1)?),
            }
        }
        AstOp::SGE(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (AstOp::BVV(arc), AstOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_ge(arc1))?),
                _ => Ok(ctx.sge(arc, arc1)?),
            }
        }
        AstOp::FpLt(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(arc), AstOp::FPV(arc1)) => Ok(ctx.boolv(arc.lt(arc1))?),
                _ => Ok(ctx.fp_lt(arc, arc1)?),
            }
        }
        AstOp::FpLeq(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(arc), AstOp::FPV(arc1)) => Ok(ctx.boolv(arc.leq(arc1))?),
                _ => Ok(ctx.fp_leq(arc, arc1)?),
            }
        }
        AstOp::FpGt(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(arc), AstOp::FPV(arc1)) => Ok(ctx.boolv(arc.gt(arc1))?),
                _ => Ok(ctx.fp_gt(arc, arc1)?),
            }
        }
        AstOp::FpGeq(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(arc), AstOp::FPV(arc1)) => Ok(ctx.boolv(arc.geq(arc1))?),
                _ => Ok(ctx.fp_geq(arc, arc1)?),
            }
        }
        AstOp::FpIsNan(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(arc) => Ok(ctx.boolv(arc.is_nan())?),
                _ => Ok(ctx.fp_is_nan(arc)?),
            }
        }
        AstOp::FpIsInf(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(arc) => Ok(ctx.boolv(arc.is_infinity())?),
                _ => Ok(ctx.fp_is_inf(arc)?),
            }
        }
        AstOp::StrContains(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` contains `substring`
                (AstOp::StringV(input_string), AstOp::StringV(substring)) => {
                    Ok(ctx.boolv(input_string.contains(substring))?)
                }
                _ => Ok(ctx.str_contains(arc, arc1)?),
            }
        }
        AstOp::StrPrefixOf(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` starts with `prefix substring`
                (AstOp::StringV(prefix), AstOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.starts_with(prefix))?)
                }
                _ => Ok(ctx.str_prefix_of(arc, arc1)?),
            }
        }
        AstOp::StrSuffixOf(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` ends with `suffix substring`
                (AstOp::StringV(suffix), AstOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.ends_with(suffix))?)
                }
                _ => Ok(ctx.str_suffix_of(arc, arc1)?),
            }
        }
        AstOp::StrIsDigit(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::StringV(input_string) => {
                    if input_string.is_empty() {
                        return Ok(ctx.boolv(false)?);
                    }
                    // is_numeric() is Unicode-aware and will also return true for non-ASCII numeric characters like Z3
                    Ok(ctx.boolv(input_string.chars().all(|c| c.is_numeric()))?)
                }
                _ => Ok(ctx.str_is_digit(arc)?),
            }
        }

        AstOp::ITE(..) => {
            let cond = state.get_child_simplified(0)?;
            let early_then = state.get_child_available(1);
            let early_else = state.get_child_available(2);

            match (cond.op(), early_then.op(), early_else.op()) {
                // Concrete condition cases
                (AstOp::BoolV(true), _, _) => state.get_child_simplified(1),
                (AstOp::BoolV(false), _, _) => state.get_child_simplified(2),

                // Same branch cases
                (_, _, _) if early_then == early_else => state.get_child_simplified(1),

                // Known then/else cases
                (_, AstOp::BoolV(true), AstOp::BoolV(false)) => Ok(cond.clone()),
                // ite(c, false, true) -> !c; rerun so the produced Not canonicalizes.
                (_, AstOp::BoolV(false), AstOp::BoolV(true)) => state.rerun(ctx.not(cond)?),

                // When condition equals one branch with concrete other branch
                (cond_op, AstOp::BoolV(true), else_op) if else_op == cond_op => Ok(cond.clone()),
                (cond_op, AstOp::BoolV(false), else_op) if else_op == cond_op => Ok(ctx.false_()?),
                (cond_op, then_op, AstOp::BoolV(true)) if then_op == cond_op => Ok(ctx.true_()?),
                (cond_op, then_op, AstOp::BoolV(false)) if then_op == cond_op => Ok(cond.clone()),

                // Default case
                _ => Ok(ctx.ite(
                    cond,
                    state.get_child_simplified(1)?,
                    state.get_child_simplified(2)?,
                )?),
            }
        }
        _ => unreachable!("non-boolean op dispatched to simplify_bool"),
    }
}

fn simplify_bv<'c>(
    state: &mut SimplifyState<'c>,
    error_on_dbz: bool,
) -> Result<AstRef<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let bv_expr = state.expr.clone();

    match bv_expr.op() {
        AstOp::BVS(..) | AstOp::BVV(..) => Ok(bv_expr),
        AstOp::Not(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::BVV(value) => Ok(ctx.bvv((!value.clone())?)?),
                _ => Ok(ctx.not(arc)?),
            }
        }
        AstOp::And(_) => {
            // Simplify all children in one batch to avoid quadratic re-runs.
            let simplified = state.get_all_simplified()?;

            let size = simplified[0].size();

            // Flatten nested Ands, fold constants, remove identities, detect absorber
            let mut bvv_acc: Option<BitVec> = None;
            let mut sym_args: Vec<AstRef<'c>> = Vec::new();

            for arg in &simplified {
                match arg.op() {
                    AstOp::And(inner_args) => {
                        for inner in inner_args {
                            match inner.op() {
                                AstOp::BVV(v) if v.is_zero() => {
                                    return Ok(ctx.bvv(BitVec::zeros(size))?);
                                }
                                AstOp::BVV(v) if v.is_all_ones() => {}
                                AstOp::BVV(v) => {
                                    bvv_acc = Some(match bvv_acc {
                                        Some(acc) => (acc & v.clone())?,
                                        None => v.clone(),
                                    });
                                }
                                _ => sym_args.push(inner.clone()),
                            }
                        }
                    }
                    AstOp::BVV(v) if v.is_zero() => {
                        return Ok(ctx.bvv(BitVec::zeros(size))?);
                    }
                    AstOp::BVV(v) if v.is_all_ones() => {}
                    AstOp::BVV(v) => {
                        bvv_acc = Some(match bvv_acc {
                            Some(acc) => (acc & v.clone())?,
                            None => v.clone(),
                        });
                    }
                    _ => sym_args.push(arg.clone()),
                }
            }

            // Deduplicate (And is idempotent: x & x = x)
            {
                let mut seen = ahash::AHashSet::with_capacity(sym_args.len());
                sym_args.retain(|arg| seen.insert(arg.hash()));
            }

            // Check for x & ¬x = 0 using a hash set for O(n) lookup
            {
                let hashes: ahash::AHashSet<u64> = sym_args.iter().map(|a| a.hash()).collect();
                for arg in &sym_args {
                    if let AstOp::Not(inner) = arg.op()
                        && hashes.contains(&inner.hash())
                    {
                        return Ok(ctx.bvv(BitVec::zeros(size))?);
                    }
                }
            }

            // Check folded BVV for absorber/identity
            if let Some(ref bvv) = bvv_acc {
                if bvv.is_zero() {
                    return Ok(ctx.bvv(BitVec::zeros(size))?);
                }
                if !bvv.is_all_ones() {
                    sym_args.push(ctx.bvv(bvv.clone())?);
                }
            }

            // Check if anything changed
            let changed = sym_args.len() != simplified.len()
                || sym_args
                    .iter()
                    .zip(simplified.iter())
                    .any(|(a, b)| a.hash() != b.hash());

            match sym_args.len() {
                0 => Ok(ctx.bvv(BitVec::from_biguint_trunc(
                    &((BigUint::one() << size) - BigUint::one()),
                    size,
                ))?),
                1 => Ok(sym_args.into_iter().next().unwrap()),
                2 => {
                    let (a, b) = (&sym_args[0], &sym_args[1]);
                    match (a.op(), b.op()) {
                        // Distribute AND over CONCAT when one operand is constant
                        (AstOp::BVV(const_val), AstOp::Concat(concat_args))
                        | (AstOp::Concat(concat_args), AstOp::BVV(const_val)) => {
                            let mut parts = Vec::with_capacity(concat_args.len());
                            let mut offset = 0u32;
                            for arg in concat_args.iter().rev() {
                                let arg_size = arg.size();
                                let const_part =
                                    const_val.extract(offset, offset + arg_size - 1)?;
                                parts.push(ctx.and2(&ctx.bvv(const_part)?, arg)?);
                                offset += arg_size;
                            }
                            parts.reverse();
                            state.rerun(ctx.concat(parts)?)
                        }

                        // Distribute AND over zero-extend when one operand is constant
                        (AstOp::BVV(const_val), AstOp::ZeroExt(inner, ext_size))
                        | (AstOp::ZeroExt(inner, ext_size), AstOp::BVV(const_val)) => {
                            let inner_size = inner.size();
                            let const_inner = const_val.extract(0, inner_size - 1)?;
                            let inner_and = ctx.and2(&ctx.bvv(const_inner)?, inner)?;
                            let zero_extended = ctx.zero_ext(&inner_and, *ext_size)?;
                            state.rerun(zero_extended)
                        }

                        // rotate_shift_mask: ((A << a) | (A >> (N - a))) & mask
                        (AstOp::Or(or_args), AstOp::BVV(mask_val))
                        | (AstOp::BVV(mask_val), AstOp::Or(or_args))
                            if or_args.len() == 2 =>
                        {
                            let (or_lhs, or_rhs) = (&or_args[0], &or_args[1]);
                            match (or_lhs.op(), or_rhs.op()) {
                                (
                                    AstOp::ShL(shl_inner, shl_amt),
                                    AstOp::LShR(lshr_inner, lshr_amt),
                                )
                                | (
                                    AstOp::LShR(lshr_inner, lshr_amt),
                                    AstOp::ShL(shl_inner, shl_amt),
                                ) if shl_inner.hash() == lshr_inner.hash() => {
                                    if let (AstOp::BVV(shl_val), AstOp::BVV(lshr_val)) =
                                        (shl_amt.op(), lshr_amt.op())
                                    {
                                        if let (Some(lshift), Some(rshift)) =
                                            (shl_val.to_u64(), lshr_val.to_u64())
                                        {
                                            let bitwidth = a.size() as u64;
                                            if lshift + rshift == bitwidth
                                                && (bitwidth == 32 || bitwidth == 64)
                                            {
                                                let mask_big = mask_val.to_biguint();
                                                let full_mask = if bitwidth == 64 {
                                                    BigUint::from(u64::MAX)
                                                } else {
                                                    BigUint::from(u32::MAX)
                                                };
                                                let unrotated = ((&mask_big >> lshift as usize)
                                                    | ((&mask_big << rshift as usize)
                                                        & &full_mask))
                                                    & &full_mask;

                                                let unrotated_bvv =
                                                    ctx.bvv(BitVec::from_biguint_trunc(
                                                        &unrotated,
                                                        bitwidth as u32,
                                                    ))?;
                                                let masked_a =
                                                    ctx.and2(shl_inner.clone(), unrotated_bvv)?;
                                                let new_shl =
                                                    ctx.shl(&masked_a, shl_amt.clone())?;
                                                let new_lshr =
                                                    ctx.lshr(&masked_a, lshr_amt.clone())?;
                                                let result = ctx.or2(new_shl, new_lshr)?;
                                                state.rerun(result)
                                            } else if changed {
                                                state.rerun(ctx.and(sym_args)?)
                                            } else {
                                                Ok(ctx.and(sym_args)?)
                                            }
                                        } else if changed {
                                            state.rerun(ctx.and(sym_args)?)
                                        } else {
                                            Ok(ctx.and(sym_args)?)
                                        }
                                    } else if changed {
                                        state.rerun(ctx.and(sym_args)?)
                                    } else {
                                        Ok(ctx.and(sym_args)?)
                                    }
                                }
                                _ => {
                                    if changed {
                                        state.rerun(ctx.and(sym_args)?)
                                    } else {
                                        Ok(ctx.and(sym_args)?)
                                    }
                                }
                            }
                        }

                        _ => {
                            if changed {
                                state.rerun(ctx.and(sym_args)?)
                            } else {
                                Ok(ctx.and(sym_args)?)
                            }
                        }
                    }
                }
                _ => {
                    if changed {
                        state.rerun(ctx.and(sym_args)?)
                    } else {
                        Ok(ctx.and(sym_args)?)
                    }
                }
            }
        }
        AstOp::Or(_) => {
            // Simplify all children in one batch to avoid quadratic re-runs.
            let simplified = state.get_all_simplified()?;

            let size = simplified[0].size();
            let all_ones =
                BitVec::from_biguint_trunc(&((BigUint::one() << size) - BigUint::one()), size);

            // Flatten nested Ors, fold constants, remove identities, detect absorber
            let mut bvv_acc: Option<BitVec> = None;
            let mut sym_args: Vec<AstRef<'c>> = Vec::new();

            for arg in &simplified {
                match arg.op() {
                    AstOp::Or(inner_args) => {
                        for inner in inner_args {
                            match inner.op() {
                                AstOp::BVV(v) if v.is_all_ones() => {
                                    return Ok(ctx.bvv(all_ones)?);
                                }
                                AstOp::BVV(v) if v.is_zero() => {}
                                AstOp::BVV(v) => {
                                    bvv_acc = Some(match bvv_acc {
                                        Some(acc) => (acc | v.clone())?,
                                        None => v.clone(),
                                    });
                                }
                                _ => sym_args.push(inner.clone()),
                            }
                        }
                    }
                    AstOp::BVV(v) if v.is_all_ones() => {
                        return Ok(ctx.bvv(all_ones)?);
                    }
                    AstOp::BVV(v) if v.is_zero() => {}
                    AstOp::BVV(v) => {
                        bvv_acc = Some(match bvv_acc {
                            Some(acc) => (acc | v.clone())?,
                            None => v.clone(),
                        });
                    }
                    _ => sym_args.push(arg.clone()),
                }
            }

            // Deduplicate (Or is idempotent: x | x = x)
            {
                let mut seen = ahash::AHashSet::with_capacity(sym_args.len());
                sym_args.retain(|arg| seen.insert(arg.hash()));
            }

            // Check for x | ¬x = all-ones using a hash set for O(n) lookup
            {
                let hashes: ahash::AHashSet<u64> = sym_args.iter().map(|a| a.hash()).collect();
                for arg in &sym_args {
                    if let AstOp::Not(inner) = arg.op()
                        && hashes.contains(&inner.hash())
                    {
                        return Ok(ctx.bvv(all_ones)?);
                    }
                }
            }

            // Check folded BVV for absorber/identity
            if let Some(ref bvv) = bvv_acc {
                if bvv.is_all_ones() {
                    return Ok(ctx.bvv(all_ones)?);
                }
                if !bvv.is_zero() {
                    sym_args.push(ctx.bvv(bvv.clone())?);
                }
            }

            let changed = sym_args.len() != simplified.len()
                || sym_args
                    .iter()
                    .zip(simplified.iter())
                    .any(|(a, b)| a.hash() != b.hash());

            match sym_args.len() {
                0 => Ok(ctx.bvv(BitVec::zeros(size))?),
                1 => Ok(sym_args.into_iter().next().unwrap()),
                2 => {
                    let (a, b) = (&sym_args[0], &sym_args[1]);
                    match (a.op(), b.op()) {
                        // Distribute OR over CONCAT when one operand is constant
                        (AstOp::BVV(const_val), AstOp::Concat(concat_args))
                        | (AstOp::Concat(concat_args), AstOp::BVV(const_val)) => {
                            let mut parts = Vec::with_capacity(concat_args.len());
                            let mut offset = 0u32;
                            for arg in concat_args.iter().rev() {
                                let arg_size = arg.size();
                                let const_part =
                                    const_val.extract(offset, offset + arg_size - 1)?;
                                parts.push(ctx.or2(&ctx.bvv(const_part)?, arg)?);
                                offset += arg_size;
                            }
                            parts.reverse();
                            state.rerun(ctx.concat(parts)?)
                        }
                        _ => {
                            if changed {
                                state.rerun(ctx.or(sym_args)?)
                            } else {
                                Ok(ctx.or(sym_args)?)
                            }
                        }
                    }
                }
                _ => {
                    if changed {
                        state.rerun(ctx.or(sym_args)?)
                    } else {
                        Ok(ctx.or(sym_args)?)
                    }
                }
            }
        }
        AstOp::Xor(_) => {
            // Simplify all children in one batch to avoid quadratic re-runs.
            let simplified = state.get_all_simplified()?;

            let size = simplified[0].size();

            // Flatten nested Xors, fold constants, remove identities
            let mut bvv_acc: Option<BitVec> = None;
            let mut sym_args: Vec<AstRef<'c>> = Vec::new();

            for arg in &simplified {
                match arg.op() {
                    AstOp::Xor(inner_args) => {
                        for inner in inner_args {
                            match inner.op() {
                                AstOp::BVV(v) if v.is_zero() => {}
                                AstOp::BVV(v) => {
                                    bvv_acc = Some(match bvv_acc {
                                        Some(acc) => (acc ^ v.clone())?,
                                        None => v.clone(),
                                    });
                                }
                                _ => sym_args.push(inner.clone()),
                            }
                        }
                    }
                    AstOp::BVV(v) if v.is_zero() => {}
                    AstOp::BVV(v) => {
                        bvv_acc = Some(match bvv_acc {
                            Some(acc) => (acc ^ v.clone())?,
                            None => v.clone(),
                        });
                    }
                    _ => sym_args.push(arg.clone()),
                }
            }

            // Cancel pairs: x ^ x = 0
            // Count occurrences by hash; odd count means the term survives
            {
                let mut counts: ahash::AHashMap<u64, usize> =
                    ahash::AHashMap::with_capacity(sym_args.len());
                for arg in &sym_args {
                    *counts.entry(arg.hash()).or_insert(0) += 1;
                }
                let mut seen = ahash::AHashSet::with_capacity(sym_args.len());
                sym_args.retain(|arg| {
                    let h = arg.hash();
                    let count = counts.get(&h).copied().unwrap_or(0);
                    // Keep only one copy if odd count, none if even
                    if count % 2 == 1 {
                        seen.insert(h) // true on first insert, false on duplicates
                    } else {
                        false
                    }
                });
            }

            // Check folded BVV
            if let Some(ref bvv) = bvv_acc
                && !bvv.is_zero()
            {
                sym_args.push(ctx.bvv(bvv.clone())?);
            }

            let changed = sym_args.len() != simplified.len()
                || sym_args
                    .iter()
                    .zip(simplified.iter())
                    .any(|(a, b)| a.hash() != b.hash());

            match sym_args.len() {
                0 => Ok(ctx.bvv(BitVec::zeros(size))?),
                1 => Ok(sym_args.into_iter().next().unwrap()),
                2 => {
                    let (a, b) = (&sym_args[0], &sym_args[1]);
                    match (a.op(), b.op()) {
                        // ¬a ^ ¬b = a ^ b
                        (AstOp::Not(lhs), AstOp::Not(rhs)) => state.rerun(ctx.xor2(lhs, rhs)?),
                        // Distribute XOR over CONCAT when one operand is constant
                        (AstOp::BVV(const_val), AstOp::Concat(concat_args))
                        | (AstOp::Concat(concat_args), AstOp::BVV(const_val)) => {
                            let mut parts = Vec::with_capacity(concat_args.len());
                            let mut offset = 0u32;
                            for arg in concat_args.iter().rev() {
                                let arg_size = arg.size();
                                let const_part =
                                    const_val.extract(offset, offset + arg_size - 1)?;
                                parts.push(ctx.xor2(&ctx.bvv(const_part)?, arg)?);
                                offset += arg_size;
                            }
                            parts.reverse();
                            state.rerun(ctx.concat(parts)?)
                        }
                        // XOR with all-ones = NOT
                        (AstOp::BVV(v), _) if v.is_all_ones() => state.rerun(ctx.not(b.clone())?),
                        (_, AstOp::BVV(v)) if v.is_all_ones() => state.rerun(ctx.not(a.clone())?),
                        _ => {
                            if changed {
                                state.rerun(ctx.xor(sym_args)?)
                            } else {
                                Ok(ctx.xor(sym_args)?)
                            }
                        }
                    }
                }
                _ => {
                    // Check if there's an all-ones BVV among the args - if so, extract it
                    // and apply NOT to the XOR of the remaining args
                    if changed {
                        state.rerun(ctx.xor(sym_args)?)
                    } else {
                        Ok(ctx.xor(sym_args)?)
                    }
                }
            }
        }
        AstOp::Neg(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::BVV(value) => Ok(ctx.bvv((-value.clone())?)?),
                // -(-x) = x (double negation)
                AstOp::Neg(inner) => Ok(inner.clone()),
                _ => Ok(ctx.neg(arc)?),
            }
        }
        AstOp::Add(_) => {
            // Simplify all children in one batch to avoid quadratic re-runs.
            let simplified = state.get_all_simplified()?;

            let size = simplified[0].size();

            // Flatten nested Adds, fold constants, remove identities
            let mut bvv_acc: Option<BitVec> = None;
            let mut sym_args: Vec<AstRef<'c>> = Vec::new();

            for arg in &simplified {
                match arg.op() {
                    AstOp::Add(inner_args) => {
                        for inner in inner_args {
                            match inner.op() {
                                AstOp::BVV(v) if v.is_zero() => {}
                                AstOp::BVV(v) => {
                                    bvv_acc = Some(match bvv_acc {
                                        Some(acc) => (acc + v.clone())?,
                                        None => v.clone(),
                                    });
                                }
                                _ => sym_args.push(inner.clone()),
                            }
                        }
                    }
                    AstOp::BVV(v) if v.is_zero() => {}
                    AstOp::BVV(v) => {
                        bvv_acc = Some(match bvv_acc {
                            Some(acc) => (acc + v.clone())?,
                            None => v.clone(),
                        });
                    }
                    _ => sym_args.push(arg.clone()),
                }
            }

            // Check folded BVV
            if let Some(ref bvv) = bvv_acc
                && !bvv.is_zero()
            {
                sym_args.push(ctx.bvv(bvv.clone())?);
            }

            let changed = sym_args.len() != simplified.len()
                || sym_args
                    .iter()
                    .zip(simplified.iter())
                    .any(|(a, b)| a.hash() != b.hash());

            match sym_args.len() {
                0 => Ok(ctx.bvv(BitVec::zeros(size))?),
                1 => Ok(sym_args.into_iter().next().unwrap()),
                2 => {
                    let (a, b) = (&sym_args[0], &sym_args[1]);
                    match (a.op(), b.op()) {
                        // If one operand is a BVV and the other is a Sub with a BVV, combine
                        (AstOp::BVV(v), AstOp::Sub(bvv, other))
                        | (AstOp::Sub(bvv, other), AstOp::BVV(v))
                            if matches!(bvv.op(), AstOp::BVV(_)) =>
                        {
                            if let AstOp::BVV(bvv_value) = bvv.op() {
                                let combined_value = (v.clone() + bvv_value.clone())?;
                                let combined_bvv = ctx.bvv(combined_value)?;
                                state.rerun(ctx.sub(other.clone(), combined_bvv)?)
                            } else {
                                unreachable!()
                            }
                        }
                        (AstOp::BVV(v), AstOp::Sub(other, bvv))
                        | (AstOp::Sub(other, bvv), AstOp::BVV(v))
                            if matches!(bvv.op(), AstOp::BVV(_)) =>
                        {
                            if let AstOp::BVV(bvv_value) = bvv.op() {
                                let combined_value = (v.clone() - bvv_value.clone())?;
                                let combined_bvv = ctx.bvv(combined_value)?;
                                state.rerun(ctx.add(other.clone(), combined_bvv)?)
                            } else {
                                unreachable!()
                            }
                        }
                        _ => {
                            if changed {
                                state.rerun(ctx.add_many(sym_args)?)
                            } else {
                                Ok(ctx.add_many(sym_args)?)
                            }
                        }
                    }
                }
                _ => {
                    if changed {
                        state.rerun(ctx.add_many(sym_args)?)
                    } else {
                        Ok(ctx.add_many(sym_args)?)
                    }
                }
            }
        }
        AstOp::Sub(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::BVV(value1), AstOp::BVV(value2)) => {
                    Ok(ctx.bvv((value1.clone() - value2.clone())?)?)
                }
                (AstOp::Sub(inner_lhs, inner_rhs), AstOp::BVV(v))
                    if matches!(inner_rhs.op(), AstOp::BVV(_)) =>
                {
                    // (a - b) - c  => a - (b + c)
                    if let AstOp::BVV(b_val) = inner_rhs.op() {
                        let combined_value = (b_val.clone() + v.clone())?;
                        let combined_bvv = ctx.bvv(combined_value)?;
                        let new_sub = ctx.sub(inner_lhs.clone(), combined_bvv)?;
                        state.rerun(new_sub)
                    } else {
                        unreachable!()
                    }
                }
                (AstOp::Add(add_args), AstOp::BVV(v)) => {
                    // Find a BVV among the Add args to combine with
                    if let Some(bvv_idx) = add_args
                        .iter()
                        .position(|a| matches!(a.op(), AstOp::BVV(_)))
                    {
                        if let AstOp::BVV(b_val) = add_args[bvv_idx].op() {
                            // (sum + b) - c => sum + (b - c)
                            let combined_value = (b_val.clone() - v.clone())?;
                            let combined_bvv = ctx.bvv(combined_value)?;
                            let mut new_args: Vec<AstRef<'c>> = add_args
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != bvv_idx)
                                .map(|(_, a)| a.clone())
                                .collect();
                            new_args.push(combined_bvv);
                            state.rerun(ctx.add_many(new_args)?)
                        } else {
                            unreachable!()
                        }
                    } else {
                        Ok(ctx.sub(arc, arc1)?)
                    }
                }
                (_, AstOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                (lhs_op, rhs_op) if lhs_op == rhs_op => Ok(ctx.bvv(BitVec::zeros(arc.size()))?),
                _ => Ok(ctx.sub(arc, arc1)?),
            }
        }
        AstOp::Mul(_) => {
            // Simplify all children in one batch to avoid quadratic re-runs.
            let simplified = state.get_all_simplified()?;

            let size = simplified[0].size();

            // Flatten nested Muls, fold constants, remove identities, detect absorber
            let mut bvv_acc: Option<BitVec> = None;
            let mut sym_args: Vec<AstRef<'c>> = Vec::new();

            for arg in &simplified {
                match arg.op() {
                    AstOp::Mul(inner_args) => {
                        for inner in inner_args {
                            match inner.op() {
                                AstOp::BVV(v) if v.is_zero() => {
                                    return Ok(ctx.bvv(BitVec::zeros(size))?);
                                }
                                AstOp::BVV(v) if v.to_u64() == Some(1) => {}
                                AstOp::BVV(v) => {
                                    bvv_acc = Some(match bvv_acc {
                                        Some(acc) => (acc * v.clone())?,
                                        None => v.clone(),
                                    });
                                }
                                _ => sym_args.push(inner.clone()),
                            }
                        }
                    }
                    AstOp::BVV(v) if v.is_zero() => {
                        return Ok(ctx.bvv(BitVec::zeros(size))?);
                    }
                    AstOp::BVV(v) if v.to_u64() == Some(1) => {}
                    AstOp::BVV(v) => {
                        bvv_acc = Some(match bvv_acc {
                            Some(acc) => (acc * v.clone())?,
                            None => v.clone(),
                        });
                    }
                    _ => sym_args.push(arg.clone()),
                }
            }

            // Check folded BVV
            if let Some(ref bvv) = bvv_acc {
                if bvv.is_zero() {
                    return Ok(ctx.bvv(BitVec::zeros(size))?);
                }
                if bvv.to_u64() != Some(1) {
                    sym_args.push(ctx.bvv(bvv.clone())?);
                }
            }

            let changed = sym_args.len() != simplified.len()
                || sym_args
                    .iter()
                    .zip(simplified.iter())
                    .any(|(a, b)| a.hash() != b.hash());

            match sym_args.len() {
                0 => Ok(ctx.bvv(BitVec::from_prim_with_size(1u64, size)?)?),
                1 => Ok(sym_args.into_iter().next().unwrap()),
                _ => {
                    if changed {
                        state.rerun(ctx.mul_many(sym_args)?)
                    } else {
                        Ok(ctx.mul_many(sym_args)?)
                    }
                }
            }
        }
        AstOp::UDiv(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (_, AstOp::BVV(v)) if error_on_dbz && v.is_zero() => {
                    Err(SimplifyError::Error(ClarirsError::DivisionByZero))
                }
                (AstOp::BVV(value1), AstOp::BVV(value2)) if !value2.is_zero() => {
                    Ok(ctx.bvv((value1.clone() / value2.clone())?)?)
                }
                (_, AstOp::BVV(v)) if v.to_u64() == Some(1) => Ok(arc.clone()),
                _ => Ok(ctx.udiv(arc, arc1)?),
            }
        }
        AstOp::SDiv(..) => {
            let (dividend_ast, divisor_ast) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (dividend_ast.op(), divisor_ast.op()) {
                (_, AstOp::BVV(v)) if error_on_dbz && v.is_zero() => {
                    Err(SimplifyError::Error(ClarirsError::DivisionByZero))
                }
                (AstOp::BVV(dividend_val), AstOp::BVV(divisor_val)) if !divisor_val.is_zero() => {
                    Ok(ctx.bvv((dividend_val.sdiv(divisor_val))?)?)
                }
                (_, AstOp::BVV(v)) if v.to_u64() == Some(1) => Ok(dividend_ast.clone()),
                _ => Ok(ctx.sdiv(dividend_ast, divisor_ast)?),
            }
        }
        AstOp::URem(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::BVV(value1), AstOp::BVV(value2)) => Ok(ctx.bvv(value1.urem(value2))?),
                _ => Ok(ctx.urem(arc, arc1)?),
            }
        }
        AstOp::SRem(..) => {
            let (dividend_ast, divisor_ast) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (dividend_ast.op(), divisor_ast.op()) {
                (AstOp::BVV(dividend_val), AstOp::BVV(divisor_val)) => {
                    Ok(ctx.bvv((dividend_val.srem(divisor_val))?)?)
                }
                _ => Ok(ctx.srem(dividend_ast, divisor_ast)?),
            }
        }
        AstOp::ShL(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (AstOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero
                (_, AstOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),

                // Simplify shift left of zero-extended value when shift amount is >= extension size
                // (shl (zero_extend n x) m) where m >= n
                // The n zero-extended MSBs are shifted out, inner is shifted left by (m-n),
                // and m zero bits appear at the LSB side.
                // Result: concat(shl(inner, m-n), BVV(0, m)) truncated to total_size
                // Which is: concat(extract(inner_size-1-(m-n), 0, inner), BVV(0, m))
                // Simplified: concat(shl(inner, m-n), BVV(0, ext_size))
                (AstOp::ZeroExt(inner, ext_size), AstOp::BVV(shift_amt))
                    if { shift_amt.to_u64().unwrap_or(0) as u32 >= *ext_size } =>
                {
                    let shift_val = shift_amt.to_u64().unwrap_or(0) as u32;
                    let total_size = inner.size() + ext_size;

                    // The zero-extended MSB bits are shifted out entirely
                    let inner_shift = shift_val - ext_size;
                    if inner_shift >= inner.size() {
                        // Everything gets shifted out
                        Ok(ctx.bvv(BitVec::zeros(total_size))?)
                    } else {
                        // Shift the inner value left by (m - ext_size), then concatenate
                        // with ext_size zero bits at the bottom (LSB side)
                        let shifted_inner = if inner_shift == 0 {
                            inner.clone()
                        } else {
                            ctx.shl(
                                inner,
                                &ctx.bvv(BitVec::from_prim_with_size(
                                    inner_shift as u64,
                                    inner.size(),
                                )?)?,
                            )?
                        };
                        // Zeros go at the bottom (LSB), shifted_inner goes at the top (MSB)
                        let zero_bottom = ctx.bvv(BitVec::zeros(*ext_size))?;
                        state.rerun(ctx.concat(vec![shifted_inner, zero_bottom])?)
                    }
                }

                // Fully concrete case
                (AstOp::BVV(value), AstOp::BVV(shift_amount)) => {
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
        AstOp::LShR(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (AstOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero
                (_, AstOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),

                // Detect bit extraction pattern: (lshr (shl x n) m)
                // This extracts bits from position (m) to position (size - 1 - n) of x
                (AstOp::ShL(inner, shl_amt), AstOp::BVV(shr_amt)) => {
                    if let AstOp::BVV(shl_val) = shl_amt.op() {
                        let shl_u32 = shl_val.to_u64().unwrap_or(0) as u32;
                        let shr_u32 = shr_amt.to_u64().unwrap_or(0) as u32;
                        let size = arc.size();

                        if shl_u32 + shr_u32 >= size {
                            // All bits get shifted out, result is zero
                            Ok(ctx.bvv(BitVec::zeros(size))?)
                        } else {
                            // This extracts bits from the original value
                            // After left shift by n, then right shift by m:
                            // - The highest bit that remains is at position (size - 1 - shl_u32)
                            // - The lowest bit that remains is at position shr_u32
                            // - The result width is (size - shl_u32 - shr_u32)
                            let high = size - 1 - shl_u32;
                            let low = shr_u32;

                            // Special handling for zero-extended values
                            if let AstOp::ZeroExt(inner_val, _) = inner.op() {
                                let inner_size = inner_val.size();

                                if low >= inner_size {
                                    // All extracted bits are from the zero-extended part
                                    Ok(ctx.bvv(BitVec::zeros(size))?)
                                } else if high < inner_size {
                                    // All extracted bits are from the original value
                                    let extracted = ctx.extract(inner_val, high, low)?;
                                    // Need to zero-pad to get back to the expected size
                                    if extracted.size() < size {
                                        state.rerun(
                                            ctx.zero_ext(&extracted, size - extracted.size())?,
                                        )
                                    } else {
                                        Ok(extracted)
                                    }
                                } else {
                                    // Extraction spans both original and zero-extended parts
                                    // Extract what we can from the original value
                                    let extracted = ctx.extract(inner_val, inner_size - 1, low)?;
                                    // Zero-extend to the final size
                                    state.rerun(ctx.zero_ext(&extracted, size - extracted.size())?)
                                }
                            } else {
                                // Regular extraction from non-zero-extended value
                                let extracted = ctx.extract(inner, high, low)?;
                                // Need to zero-pad to get back to the expected size
                                if extracted.size() < size {
                                    state.rerun(ctx.zero_ext(&extracted, size - extracted.size())?)
                                } else {
                                    Ok(extracted)
                                }
                            }
                        }
                    } else {
                        Ok(ctx.lshr(arc, arc1)?)
                    }
                }

                // Fully concrete case
                (AstOp::BVV(value), AstOp::BVV(shift_amount)) => {
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
        AstOp::AShR(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (AstOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Zero shift amount
                (_, AstOp::BVV(v)) if v.is_zero() => Ok(arc.clone()),
                // Fully concrete case
                (AstOp::BVV(value), AstOp::BVV(shift_amount)) => {
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
        AstOp::RotateLeft(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (AstOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero or multiple of size
                (_, AstOp::BVV(v))
                    if v.is_zero() || v.to_bigint() % arc.size() == BigInt::zero() =>
                {
                    Ok(arc.clone())
                }
                // Fully concrete case
                (AstOp::BVV(value_bv), AstOp::BVV(rotate_bv)) => {
                    let rotate_u32 = rotate_bv.to_u64().unwrap_or(0) as u32;
                    let rotated_bv = value_bv.rotate_left(rotate_u32)?;
                    Ok(ctx.bvv(rotated_bv)?)
                }
                // Nested rotation with concrete amounts - combine them
                // rotate_left(rotate_left(x, c1), c2) => rotate_left(x, (c1 + c2) % size)
                (AstOp::RotateLeft(inner, inner_amt), AstOp::BVV(outer_amt)) => {
                    if let AstOp::BVV(inner_amt_val) = inner_amt.op() {
                        let size = arc.size();
                        let combined_amt = (inner_amt_val.to_bigint() + outer_amt.to_bigint())
                            % BigInt::from(size);
                        let combined_amt_bv = BitVec::from_bigint(&combined_amt, arc1.size())?;
                        state.rerun(ctx.rotate_left(inner.clone(), ctx.bvv(combined_amt_bv)?)?)
                    } else {
                        // Inner rotation amount is not concrete, fall through
                        let rotate_amount_u32 = outer_amt.to_u64().unwrap_or(0) as u32;
                        let bottom = ctx.extract(&arc, rotate_amount_u32 - 1, 0)?;
                        let top = ctx.extract(&arc, arc.size() - 1, rotate_amount_u32)?;
                        state.rerun(ctx.concat2(bottom, top)?)
                    }
                }
                // Fallback case
                _ => Ok(ctx.rotate_left(arc, arc1)?),
            }
        }
        AstOp::RotateRight(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Base value is zero
                (AstOp::BVV(v), _) if v.is_zero() => Ok(arc),
                // Shift by zero or multiple of size
                (_, AstOp::BVV(v))
                    if v.is_zero() || v.to_bigint() % arc.size() == BigInt::zero() =>
                {
                    Ok(arc.clone())
                }
                // Fully concrete case
                (AstOp::BVV(value_bv), AstOp::BVV(rotate_amount_bv)) => {
                    let rotate_u32 = rotate_amount_bv.to_u64().unwrap_or(0) as u32;
                    let rotated_bv = value_bv.rotate_right(rotate_u32)?;
                    Ok(ctx.bvv(rotated_bv)?)
                }
                // Nested rotation with concrete amounts - combine them
                // rotate_right(rotate_right(x, c1), c2) => rotate_right(x, (c1 + c2) % size)
                (AstOp::RotateRight(inner, inner_amt), AstOp::BVV(outer_amt)) => {
                    if let AstOp::BVV(inner_amt_val) = inner_amt.op() {
                        let size = arc.size();
                        let combined_amt = (inner_amt_val.to_bigint() + outer_amt.to_bigint())
                            % BigInt::from(size);
                        let combined_amt_bv = BitVec::from_bigint(&combined_amt, arc1.size())?;
                        state.rerun(ctx.rotate_right(inner.clone(), ctx.bvv(combined_amt_bv)?)?)
                    } else {
                        // Inner rotation amount is not concrete, fall through
                        let rotate_amount_u32 = outer_amt.to_u64().unwrap_or(0) as u32;
                        let bottom = ctx.extract(&arc, arc.size() - rotate_amount_u32, 0)?;
                        let top =
                            ctx.extract(&arc, arc.size() - 1, arc.size() - rotate_amount_u32)?;
                        state.rerun(ctx.concat2(top, bottom)?)
                    }
                }
                // Fallback case
                _ => Ok(ctx.rotate_right(arc, arc1)?),
            }
        }
        AstOp::ZeroExt(_, num_bits) => {
            let arc = state.get_child_simplified(0)?;
            match (arc.op(), num_bits) {
                // Zero extension
                (_, 0) => Ok(arc.clone()),
                // Concrete BVV case
                (AstOp::BVV(value), _) => Ok(ctx.bvv(value.zero_extend(*num_bits)?)?),
                // Nested ZeroExt - combine extensions
                (AstOp::ZeroExt(inner, inner_num_bits), _) => {
                    let total_ext = inner_num_bits + num_bits;
                    state.rerun(ctx.zero_ext(inner, total_ext)?)
                }
                // Propogate over ITE when the children are BVVs
                (AstOp::ITE(cond, then_bv, else_bv), _) => {
                    let then_ext = ctx.zero_ext(then_bv, *num_bits)?;
                    let else_ext = ctx.zero_ext(else_bv, *num_bits)?;
                    state.rerun(ctx.ite(cond, &then_ext, &else_ext)?)
                }
                // Symbolic case
                (_, _) => Ok(ctx.zero_ext(arc, *num_bits)?),
            }
        }
        AstOp::SignExt(_, num_bits) => {
            let arc = state.get_child_simplified(0)?;
            match (arc.op(), num_bits) {
                // Sign extension
                (_, 0) => Ok(arc.clone()),
                // Concrete BVV case
                (AstOp::BVV(value), _) => Ok(ctx.bvv(value.sign_extend(*num_bits)?)?),
                // Nested SignExt - combine extensions
                (AstOp::SignExt(inner, inner_num_bits), _) => {
                    let total_ext = inner_num_bits + num_bits;
                    state.rerun(ctx.sign_ext(inner, total_ext)?)
                }
                // Fallback case
                (_, _) => Ok(ctx.sign_ext(arc, *num_bits)?),
            }
        }
        AstOp::Extract(_, high, low) => {
            let arc = state.get_child_simplified(0)?;

            // If the extract bounds are the entire BV, return the inner value as-is
            if *high == arc.size() - 1 && *low == 0 {
                return Ok(arc);
            }

            match arc.op() {
                // Concrete BVV case
                AstOp::BVV(value) => Ok(ctx.bvv(value.extract(*low, *high)?)?),

                // Nested Extract - combine extracts
                AstOp::Extract(inner, _, inner_low) => {
                    // Calculate new high and low for the inner extract
                    let new_high = inner_low + *high;
                    let new_low = inner_low + *low;
                    state.rerun(ctx.extract(inner, new_high, new_low)?)
                }

                // Propagate extract(n, 0, ...) through add/sub
                // extract(n, 0, a + b + ...) = extract(n, 0, a) + extract(n, 0, b) + ...
                // This is valid because the low bits of add/sub only depend on the low bits of the operands
                AstOp::Add(add_args) if *low == 0 => {
                    let extracted: Vec<AstRef<'c>> = add_args
                        .iter()
                        .map(|a| ctx.extract(a, *high, 0))
                        .collect::<Result<_, _>>()?;
                    state.rerun(ctx.add_many(extracted)?)
                }
                AstOp::Sub(lhs, rhs) if *low == 0 => {
                    let lhs_extracted = ctx.extract(lhs, *high, 0)?;
                    let rhs_extracted = ctx.extract(rhs, *high, 0)?;
                    state.rerun(ctx.sub(&lhs_extracted, &rhs_extracted)?)
                }

                // Propagate extract through bitwise operations
                // extract(n, m, a & b & ...) = extract(n, m, a) & extract(n, m, b) & ...
                AstOp::And(and_args) => {
                    let extracted: Vec<AstRef<'c>> = and_args
                        .iter()
                        .map(|a| ctx.extract(a, *high, *low))
                        .collect::<Result<_, _>>()?;
                    state.rerun(ctx.and(extracted)?)
                }
                // extract(n, m, a | b | ...) = extract(n, m, a) | extract(n, m, b) | ...
                AstOp::Or(or_args) => {
                    let extracted: Vec<AstRef<'c>> = or_args
                        .iter()
                        .map(|a| ctx.extract(a, *high, *low))
                        .collect::<Result<_, _>>()?;
                    state.rerun(ctx.or(extracted)?)
                }
                // extract(n, m, a ^ b ^ ...) = extract(n, m, a) ^ extract(n, m, b) ^ ...
                AstOp::Xor(xor_args) => {
                    let extracted: Vec<AstRef<'c>> = xor_args
                        .iter()
                        .map(|a| ctx.extract(a, *high, *low))
                        .collect::<Result<_, _>>()?;
                    state.rerun(ctx.xor(extracted)?)
                }
                // extract(n, m, ~a) = ~extract(n, m, a)
                AstOp::Not(inner) => {
                    let inner_extracted = ctx.extract(inner, *high, *low)?;
                    state.rerun(ctx.not(&inner_extracted)?)
                }

                // Propogate through ITE
                AstOp::ITE(cond, then_bv, else_bv) => {
                    let then_extracted = ctx.extract(then_bv, *high, *low)?;
                    let else_extracted = ctx.extract(else_bv, *high, *low)?;
                    state.rerun(ctx.ite(cond, &then_extracted, &else_extracted)?)
                }

                // ZeroExt cases
                // If extracting from the original bits (not the extended zero bits)
                AstOp::ZeroExt(inner, _) if *high < inner.size() => {
                    state.rerun(ctx.extract(inner, *high, *low)?)
                }
                // If extracting only from the extended zero bits
                AstOp::ZeroExt(inner, _) if *low >= inner.size() => {
                    Ok(ctx.bvv(BitVec::zeros(*high - *low + 1))?)
                }
                // If extracting bits that span original and extended parts
                AstOp::ZeroExt(inner, _) => {
                    let inner_size = inner.size();
                    // Extract what we can from the original bits
                    let extracted = ctx.extract(inner, inner_size - 1, *low)?;
                    // Zero-extend to the final size
                    state.rerun(ctx.zero_ext(&extracted, *high - inner_size + 1)?)
                }

                // SignExt cases
                // If extracting from the original bits (not the extended sign bits)
                AstOp::SignExt(inner, _) if *high < inner.size() => {
                    state.rerun(ctx.extract(inner, *high, *low)?)
                }
                // If extracting only from the extended sign bits
                AstOp::SignExt(inner, _) if *low >= inner.size() => {
                    let sign_bit = ctx.extract(inner, inner.size() - 1, inner.size() - 1)?;
                    // Replicate the sign bit for the extracted width
                    let width = *high - *low + 1;
                    let sign_bits: Vec<_> = (0..width).map(|_| sign_bit.clone()).collect();
                    Ok(ctx.concat(sign_bits)?)
                }

                // N-ary Concat cases
                AstOp::Concat(args) => {
                    // Compute cumulative sizes from the right (LSB side)
                    // For concat(a, b, c), sizes are [a.size()+b.size()+c.size(), b.size()+c.size(), c.size(), 0]
                    let mut cumulative_sizes: Vec<u32> = Vec::with_capacity(args.len() + 1);
                    let mut sum = 0u32;
                    for arg in args.iter().rev() {
                        cumulative_sizes.push(sum);
                        sum += arg.size();
                    }
                    cumulative_sizes.push(sum);
                    cumulative_sizes.reverse();
                    // Now cumulative_sizes[i] = total size of args[i..] (bits from position 0 to end of arg i)

                    // Find which args the extract spans
                    // The extract covers bits [low, high] inclusive
                    // arg[i] covers bits [cumulative_sizes[i+1], cumulative_sizes[i] - 1]
                    let mut first_idx = None;
                    let mut last_idx = None;
                    for i in 0..args.len() {
                        let arg_high = cumulative_sizes[i] - 1; // highest bit of this arg
                        let arg_low = cumulative_sizes[i + 1]; // lowest bit of this arg

                        if *high >= arg_low && *low <= arg_high {
                            if first_idx.is_none() {
                                first_idx = Some(i);
                            }
                            last_idx = Some(i);
                        }
                    }

                    match (first_idx, last_idx) {
                        (Some(first), Some(last)) if first == last => {
                            // Extract is entirely within one arg
                            let arg_low = cumulative_sizes[first + 1];
                            state.rerun(ctx.extract(
                                &args[first],
                                *high - arg_low,
                                *low - arg_low,
                            )?)
                        }
                        (Some(first), Some(last)) => {
                            // Extract spans multiple args
                            let mut parts = Vec::with_capacity(last - first + 1);
                            for i in first..=last {
                                let arg = &args[i];
                                let arg_high = cumulative_sizes[i] - 1;
                                let arg_low = cumulative_sizes[i + 1];

                                let extract_high = (*high).min(arg_high) - arg_low;
                                let extract_low = (*low).max(arg_low) - arg_low;
                                parts.push(ctx.extract(arg, extract_high, extract_low)?);
                            }
                            state.rerun(ctx.concat(parts)?)
                        }
                        _ => Ok(ctx.extract(arc, *high, *low)?),
                    }
                }
                _ => Ok(ctx.extract(arc, *high, *low)?),
            }
        }
        AstOp::Concat(_) => {
            // Simplify all children in one batch. Fetching them one at a
            // time would make simplify_inner re-run for every child and
            // turn wide Concats into a quadratic cost.
            let simplified_args = state.get_all_simplified()?;

            // Flatten nested Concats and filter zero-size args
            let mut flattened: Vec<AstRef<'c>> = Vec::new();
            for arg in simplified_args {
                if arg.size() == 0 {
                    continue;
                }
                if let AstOp::Concat(inner_args) = arg.op() {
                    flattened.extend(inner_args.iter().cloned());
                } else {
                    flattened.push(arg);
                }
            }

            // Concat(If(c, a0, b0), If(c, a1, b1), ...)
            //   -> If(c, Concat(a0, a1, ...), Concat(b0, b1, ...))
            // when every piece is an ITE guarded by the same condition. This
            // recombines values computed lane-by-lane (e.g. a word updated
            // byte-wise in memory) back into a single conditional, which is what
            // lets the surrounding arithmetic collapse.
            if flattened.len() >= 2
                && let AstOp::ITE(cond0, _, _) = flattened[0].op()
            {
                let cond_hash = cond0.hash();
                let all_same_cond = flattened
                    .iter()
                    .all(|a| matches!(a.op(), AstOp::ITE(c, _, _) if c.hash() == cond_hash));
                if all_same_cond {
                    let cond = match flattened[0].op() {
                        AstOp::ITE(c, _, _) => c.clone(),
                        _ => unreachable!(),
                    };
                    let mut thens: Vec<AstRef<'c>> = Vec::with_capacity(flattened.len());
                    let mut elses: Vec<AstRef<'c>> = Vec::with_capacity(flattened.len());
                    for a in &flattened {
                        if let AstOp::ITE(_, t, e) = a.op() {
                            thens.push(t.clone());
                            elses.push(e.clone());
                        }
                    }
                    let then_concat = ctx.concat(thens)?;
                    let else_concat = ctx.concat(elses)?;
                    return state.rerun(ctx.ite(cond, then_concat, else_concat)?);
                }
            }

            // Merge adjacent constants and adjacent extracts of the same source.
            let mut merged: Vec<AstRef<'c>> = Vec::new();
            let mut merged_extracts = false;
            for arg in flattened {
                // Concat(.., BVV(a), BVV(b)) -> Concat(.., BVV(a .. b))
                if let (Some(last), AstOp::BVV(curr_val)) = (merged.last(), arg.op())
                    && let AstOp::BVV(last_val) = last.op()
                {
                    let merged_val = last_val.concat(curr_val)?;
                    merged.pop();
                    merged.push(ctx.bvv(merged_val)?);
                    continue;
                }
                // Concat(.., Extract(hi, mid + 1, x), Extract(mid, lo, x))
                //   -> Concat(.., Extract(hi, lo, x))
                // Reassembles a value that was split into adjacent pieces, e.g. a
                // word stored/loaded byte-wise in memory. Without this, such
                // split-then-recombined values survive to the solver and can make
                // otherwise-trivial queries extremely hard.
                if let Some(last) = merged.last()
                    && let AstOp::Extract(hi_src, hi_high, hi_low) = last.op()
                    && let AstOp::Extract(lo_src, lo_high, lo_low) = arg.op()
                    && *hi_low == lo_high + 1
                    && hi_src.hash() == lo_src.hash()
                {
                    let combined = ctx.extract(hi_src, *hi_high, *lo_low)?;
                    merged.pop();
                    merged.push(combined);
                    merged_extracts = true;
                    continue;
                }
                merged.push(arg);
            }

            // Concat(BVV(0, N), rest...) -> ZeroExt(N, Concat(rest...))
            if merged.len() >= 2
                && matches!(merged[0].op(), AstOp::BVV(high_val) if high_val.is_zero())
            {
                let ext_size = merged[0].size();
                let rest: Vec<AstRef<'c>> = merged[1..].to_vec();
                let inner = if rest.len() == 1 {
                    rest.into_iter().next().unwrap()
                } else {
                    ctx.concat(rest)?
                };
                return state.rerun(ctx.zero_ext(&inner, ext_size)?);
            }

            // Handle result based on merged length
            let result = match merged.len() {
                0 => {
                    return Err(SimplifyError::Error(ClarirsError::InvalidArguments(
                        "Concat resulted in zero arguments".to_string(),
                    )));
                }
                1 => merged.into_iter().next().unwrap(),
                _ => ctx.concat(merged)?,
            };
            // Re-simplify when extracts were combined so that a now-full-range
            // Extract(size - 1, 0, x) collapses back to x.
            if merged_extracts {
                state.rerun(result)
            } else {
                Ok(result)
            }
        }
        AstOp::ByteReverse(..) => {
            let arc = state.get_child_simplified(0)?;
            // Reversing a single byte (or smaller) is the identity.
            if arc.size() <= 8 {
                return Ok(arc);
            }
            match arc.op() {
                AstOp::BVV(value) => {
                    let reversed_bits = value.reverse_bytes()?;
                    Ok(ctx.bvv(reversed_bits)?)
                }
                // Reverse(Reverse(x)) -> x
                AstOp::ByteReverse(inner) => Ok(inner.clone()),
                // Reverse(If(c, a, b)) -> If(c, Reverse(a), Reverse(b)). Pushing
                // the reverse into the branches lets it cancel/collapse there.
                AstOp::ITE(cond, then_, else_) => {
                    let new = ctx.ite(
                        cond.clone(),
                        ctx.byte_reverse(then_.clone())?,
                        ctx.byte_reverse(else_.clone())?,
                    )?;
                    state.rerun(new)
                }
                // Reverse(Concat(a, .., z)) -> Concat(Reverse(z), .., Reverse(a)).
                // Byte-order reversal commutes with Concat only when every piece
                // is byte-aligned.
                AstOp::Concat(args) if args.len() > 1 && args.iter().all(|a| a.size() % 8 == 0) => {
                    let reversed = args
                        .iter()
                        .rev()
                        .map(|a| ctx.byte_reverse(a.clone()))
                        .collect::<Result<Vec<_>, _>>()?;
                    let new = ctx.concat(reversed)?;
                    state.rerun(new)
                }
                _ => Ok(ctx.byte_reverse(arc)?),
            }
        }
        AstOp::FpToIEEEBV(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float) => {
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
        AstOp::FpToUBV(_, bit_size, fprm) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float) => {
                    // Convert the float to an unsigned integer representation (BigUint)
                    let unsigned_value = float.to_unsigned_biguint().unwrap_or(BigUint::zero());

                    // Truncate or extend the result to fit within the specified bit size
                    let result_bitvec = BitVec::from_biguint_trunc(&unsigned_value, *bit_size);

                    Ok(ctx.bvv(result_bitvec)?)
                }
                _ => Ok(ctx.fp_to_ubv(arc, *bit_size, *fprm)?), // Fallback for non-concrete values
            }
        }
        AstOp::FpToSBV(_, bit_size, fprm) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float) => {
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
        AstOp::StrLen(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::StringV(value) => {
                    // chars().count() returns the number of Unicode scalar values
                    let length = value.chars().count() as u64;
                    Ok(ctx.bvv(BitVec::from_prim_with_size(length, 64)?)?)
                }
                _ => Ok(ctx.str_len(arc)?), // Fallback to symbolic
            }
        }
        AstOp::StrIndexOf(..) => {
            let (arc, arc1, arc2) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
                state.get_child_simplified(2)?,
            );

            match (arc.op(), arc1.op(), arc2.op()) {
                (
                    AstOp::StringV(input_string),
                    AstOp::StringV(substring),
                    AstOp::BVV(start_index),
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
                _ => Ok(ctx.str_index_of(arc, arc1, arc2)?), // Fallback to symbolic
            }
        }
        AstOp::StrToBV(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::StringV(string) => {
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
                _ => Ok(ctx.str_to_bv(arc)?),
            }
        }
        AstOp::ITE(..) => {
            let (if_, then_, else_) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
                state.get_child_simplified(2)?,
            );

            // If both branches are identical, return either one
            if then_ == else_ {
                return Ok(then_.clone());
            }

            match if_.op() {
                // If the condition is a concrete boolean value, return the appropriate branch
                AstOp::BoolV(value) => {
                    if *value {
                        Ok(then_.clone())
                    } else {
                        Ok(else_.clone())
                    }
                }
                // If the condition has a Not at the top level, invert the branches
                AstOp::Not(inner) => state.rerun(ctx.ite(inner, else_, then_)?),
                _ => Ok(ctx.ite(if_, then_, else_)?),
            }
        }
        AstOp::Union(..) => {
            let (lhs, rhs) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            Ok(ctx.union(lhs, rhs)?)
        }
        AstOp::Intersection(..) => {
            let (lhs, rhs) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            Ok(ctx.intersection(lhs, rhs)?)
        }
        AstOp::Widen(..) => {
            let (lhs, rhs) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            if lhs == rhs {
                return Ok(lhs.clone());
            }
            Ok(ctx.widen(lhs, rhs)?)
        }
        _ => unreachable!("non-bitvector op dispatched to simplify_bv"),
    }
}

fn simplify_float<'c>(state: &mut SimplifyState<'c>) -> Result<AstRef<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let float_expr = state.expr.clone();

    match float_expr.op() {
        AstOp::FPS(..) | AstOp::FPV(_) => Ok(float_expr),

        AstOp::FpFP(..) => {
            let sign = state.get_child_simplified(0)?;
            let exp = state.get_child_simplified(1)?;
            let sig = state.get_child_simplified(2)?;

            // If all components are concrete, construct a concrete float
            match (sign.op(), exp.op(), sig.op()) {
                (AstOp::BVV(sign_bv), AstOp::BVV(exp_bv), AstOp::BVV(sig_bv)) => {
                    let float = Float::new(
                        !sign_bv.is_zero(), // sign is true if bit is 1
                        exp_bv.clone(),
                        sig_bv.clone(),
                    )?;
                    Ok(ctx.fpv(float)?)
                }
                _ => Ok(ctx.fp_fp(sign, exp, sig)?),
            }
        }

        AstOp::FpNeg(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float) => Ok(ctx.fpv(-*float)?),
                _ => Ok(ctx.fp_neg(arc)?),
            }
        }
        AstOp::FpAbs(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float) => Ok(ctx.fpv(float.abs())?),
                _ => Ok(ctx.fp_abs(arc)?),
            }
        }
        AstOp::FpAdd(_, _, fprm) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(float1), AstOp::FPV(float2)) => Ok(ctx.fpv(*float1 + *float2)?),
                _ => Ok(ctx.fp_add(arc, arc1, *fprm)?),
            }
        }
        AstOp::FpSub(_, _, fprm) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(float1), AstOp::FPV(float2)) => Ok(ctx.fpv(*float1 - *float2)?),
                _ => Ok(ctx.fp_sub(arc, arc1, *fprm)?),
            }
        }
        AstOp::FpMul(_, _, fprm) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(float1), AstOp::FPV(float2)) => Ok(ctx.fpv(*float1 * *float2)?),
                _ => Ok(ctx.fp_mul(arc, arc1, *fprm)?),
            }
        }
        AstOp::FpDiv(_, _, fprm) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::FPV(float1), AstOp::FPV(float2)) => Ok(ctx.fpv(*float1 / *float2)?),
                _ => Ok(ctx.fp_div(arc, arc1, *fprm)?),
            }
        }
        AstOp::FpSqrt(_, fprm) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float_val) => Ok(ctx.fpv(float_val.sqrt())?),
                _ => Ok(ctx.fp_sqrt(arc, *fprm)?),
            }
        }
        AstOp::FpToFp(_, fsort, fprm) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::FPV(float_val) if float_val.fsort() == *fsort => Ok(arc),
                AstOp::FPV(float_val) => {
                    let converted_value = float_val.convert_to_format(*fsort, *fprm)?;
                    Ok(ctx.fpv(converted_value)?)
                }
                _ => Ok(ctx.fp_to_fp(arc, *fsort, *fprm)?),
            }
        }
        AstOp::BvToFp(_, fsort) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::BVV(bv_val) => {
                    // Extract sign, exponent, and mantissa from IEEE 754 representation
                    let total_bits = bv_val.len();
                    let man_bits = fsort.mantissa;

                    // Ensure the bitvector size matches the float sort
                    if total_bits != fsort.size() {
                        return Err(SimplifyError::Error(ClarirsError::InvalidArguments(
                            format!(
                                "bitvector size {} does not match float sort size {}",
                                total_bits,
                                fsort.size()
                            ),
                        )));
                    }

                    // Extract components: sign (1 bit) | exponent (exp_bits) | mantissa (man_bits)
                    let sign_bit = bv_val.extract(total_bits - 1, total_bits - 1)?;
                    let exponent = bv_val.extract(man_bits, total_bits - 2)?;
                    let mantissa = bv_val.extract(0, man_bits - 1)?;

                    // Construct Float from components
                    let float = Float::new(
                        !sign_bit.is_zero(), // sign is true if bit is 1
                        exponent,
                        mantissa,
                    )?;
                    Ok(ctx.fpv(float)?)
                }
                _ => Ok(ctx.bv_to_fp(arc, *fsort)?),
            }
        }
        AstOp::BvToFpSigned(_, fsort, fprm) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::BVV(bv_val) => {
                    // Handle conversion from signed bitvector to float
                    let float_value =
                        Float::from_bigint_with_rounding(&bv_val.to_bigint(), *fsort, *fprm)?;
                    Ok(ctx.fpv(float_value)?)
                }
                _ => Ok(ctx.bv_to_fp_signed(arc, *fsort, *fprm)?),
            }
        }
        AstOp::BvToFpUnsigned(_, fsort, fprm) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::BVV(bv_val) => {
                    // Interpret `bv_val` as an unsigned integer and convert to float
                    let float_value =
                        Float::from_biguint_with_rounding(&bv_val.to_biguint(), *fsort, *fprm)?;
                    Ok(ctx.fpv(float_value)?)
                }
                _ => Ok(ctx.bv_to_fp_unsigned(arc, *fsort, *fprm)?),
            }
        }
        AstOp::ITE(..) => {
            let (if_, then_, else_) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
                state.get_child_simplified(2)?,
            );

            // If both branches are identical, return either one
            if then_ == else_ {
                return Ok(then_.clone());
            }

            match if_.op() {
                // If the condition is a concrete boolean value, return the appropriate branch
                AstOp::BoolV(value) => {
                    if *value {
                        Ok(then_.clone())
                    } else {
                        Ok(else_.clone())
                    }
                }
                // If the condition has a Not at the top level, invert the branches
                AstOp::Not(inner) => Ok(ctx.ite(inner, else_, then_)?),
                _ => Ok(ctx.ite(if_, then_, else_)?),
            }
        }
        _ => unreachable!("non-float op dispatched to simplify_float"),
    }
}

fn simplify_string<'c>(state: &mut SimplifyState<'c>) -> Result<AstRef<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let string_expr = state.expr.clone();

    match string_expr.op() {
        AstOp::StringS(_) | AstOp::StringV(_) => Ok(string_expr),
        AstOp::StrConcat(..) => {
            let (arc, arc1) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                (AstOp::StringV(str1), AstOp::StringV(str2)) => {
                    let concatenated = format!("{str1}{str2}");
                    Ok(ctx.stringv(concatenated)?)
                }
                _ => Ok(ctx.str_concat(arc, arc1)?),
            }
        }
        AstOp::StrSubstr(..) => {
            let (arc, arc1, arc2) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
                state.get_child_simplified(2)?,
            );
            match (arc.op(), arc1.op(), arc2.op()) {
                (AstOp::StringV(s), AstOp::BVV(start_bv), AstOp::BVV(length_bv)) => {
                    // Convert the bitvectors to usize indices.
                    let start = start_bv.to_usize().unwrap_or(0);
                    let length = length_bv.to_usize().unwrap_or(s.chars().count());
                    let num_chars = s.chars().count();

                    // If the starting index is out-of-bound (e.g., negative index wrapped to 2^64-1),
                    // then return an empty string.
                    if start >= num_chars {
                        return Ok(ctx.stringv("".to_string())?);
                    }

                    // Convert character-based indices to byte-based indices.
                    let char_start = s.chars().take(start).map(|c| c.len_utf8()).sum();
                    let char_end = s.chars().take(start + length).map(|c| c.len_utf8()).sum();

                    let substring = s.get(char_start..char_end).unwrap_or("").to_string();
                    Ok(ctx.stringv(substring)?)
                }
                _ => Ok(ctx.str_substr(arc, arc1, arc2)?),
            }
        }
        AstOp::StrReplace(..) => {
            let (arc, arc1, arc2) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
                state.get_child_simplified(2)?,
            );
            match (arc.op(), arc1.op(), arc2.op()) {
                (AstOp::StringV(initial), AstOp::StringV(pattern), AstOp::StringV(replacement)) => {
                    // Case: Replace first occurrence of `pattern` with `replacement` in `initial` as per ClariPy DONE
                    let new_value = initial.replacen(pattern, replacement, 1);
                    // Case: Replace all occurrences of `pattern` with `replacement` in `initial` LEFT
                    // let new_value = initial.replace(pattern, replacement);
                    Ok(ctx.stringv(new_value)?)
                }
                _ => Ok(ctx.str_replace(arc, arc1, arc2)?), // Fallback to symbolic StrReplace
            }
        }
        AstOp::BVToStr(..) => {
            let arc = state.get_child_simplified(0)?;
            match arc.op() {
                AstOp::BVV(value) => {
                    // Convert the BitVec value to an integer, then to a string
                    let int_value = value.to_biguint();
                    let string_value = int_value.to_string();

                    Ok(ctx.stringv(string_value)?)
                }
                _ => Ok(ctx.bv_to_str(arc)?),
            }
        }
        AstOp::ITE(..) => {
            let (if_, then_, else_) = (
                state.get_child_simplified(0)?,
                state.get_child_simplified(1)?,
                state.get_child_simplified(2)?,
            );

            // If both branches are identical, return either one
            if then_ == else_ {
                return Ok(then_.clone());
            }

            match if_.op() {
                // If the condition is a concrete boolean value, return the appropriate branch
                AstOp::BoolV(value) => {
                    if *value {
                        Ok(then_.clone())
                    } else {
                        Ok(else_.clone())
                    }
                }
                // If the condition has a Not at the top level, invert the branches
                AstOp::Not(inner) => Ok(ctx.ite(inner, else_, then_)?),
                _ => Ok(ctx.ite(if_, then_, else_)?),
            }
        }
        _ => unreachable!("non-string op dispatched to simplify_string"),
    }
}
