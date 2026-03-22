mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;

use crate::{cache::Cache, prelude::*};

pub trait Simplify<'c>: Sized {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        self.simplify_ext(true, false)
    }

    fn simplify_ext(
        &self,
        respect_annotations: bool,
        error_on_dbz: bool,
    ) -> Result<Self, ClarirsError>;
}

impl<'c> Simplify<'c> for AstRef<'c> {
    fn simplify_ext(
        &self,
        respect_annotations: bool,
        error_on_dbz: bool,
    ) -> Result<Self, ClarirsError> {
        simplify(self, respect_annotations, error_on_dbz)
    }
}

#[derive(thiserror::Error, Debug)]
enum SimplifyError<'c> {
    #[error("Missing child at index {0}")]
    MissingChild(usize),
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
        let num_children = expr.child_iter().count();
        Self {
            expr,
            children: vec![None; num_children],
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

    // All typed getters now just delegate to get_child_simplified since types are unified
    fn get_bool_simplified(&mut self, index: usize) -> Result<BoolAst<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
    }

    fn get_bv_simplified(&mut self, index: usize) -> Result<BitVecAst<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
    }

    fn get_fp_simplified(&mut self, index: usize) -> Result<FloatAst<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
    }

    fn get_string_simplified(&mut self, index: usize) -> Result<StringAst<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
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

    fn get_bool_available(&self, index: usize) -> Result<BoolAst<'c>, ClarirsError> {
        Ok(self.get_child_available(index))
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
        .get_or_insert(expr.hash(), || {
            match expr.op() {
                // Boolean ops
                AstOp::BoolS(..)
                | AstOp::BoolV(..)
                | AstOp::ULT(..)
                | AstOp::ULE(..)
                | AstOp::UGT(..)
                | AstOp::UGE(..)
                | AstOp::SLT(..)
                | AstOp::SLE(..)
                | AstOp::SGT(..)
                | AstOp::SGE(..)
                | AstOp::FpLt(..)
                | AstOp::FpLeq(..)
                | AstOp::FpGt(..)
                | AstOp::FpGeq(..)
                | AstOp::FpIsNan(..)
                | AstOp::FpIsInf(..)
                | AstOp::StrContains(..)
                | AstOp::StrPrefixOf(..)
                | AstOp::StrSuffixOf(..)
                | AstOp::StrIsDigit(..) => bool::simplify_bool(state),

                // BV ops
                AstOp::BVS(..)
                | AstOp::BVV(..)
                | AstOp::Neg(..)
                | AstOp::Add(..)
                | AstOp::Sub(..)
                | AstOp::Mul(..)
                | AstOp::UDiv(..)
                | AstOp::SDiv(..)
                | AstOp::URem(..)
                | AstOp::SRem(..)
                | AstOp::ShL(..)
                | AstOp::LShR(..)
                | AstOp::AShR(..)
                | AstOp::RotateLeft(..)
                | AstOp::RotateRight(..)
                | AstOp::Extract(..)
                | AstOp::ZeroExt(..)
                | AstOp::SignExt(..)
                | AstOp::Concat(..)
                | AstOp::ByteReverse(..)
                | AstOp::FpToIEEEBV(..)
                | AstOp::FpToUBV(..)
                | AstOp::FpToSBV(..)
                | AstOp::StrLen(..)
                | AstOp::StrIndexOf(..)
                | AstOp::StrToBV(..)
                | AstOp::Union(..)
                | AstOp::Intersection(..)
                | AstOp::Widen(..) => bv::simplify_bv(state, error_on_dbz),

                // Float ops
                AstOp::FPS(..)
                | AstOp::FPV(..)
                | AstOp::FpNeg(..)
                | AstOp::FpAbs(..)
                | AstOp::FpAdd(..)
                | AstOp::FpSub(..)
                | AstOp::FpMul(..)
                | AstOp::FpDiv(..)
                | AstOp::FpSqrt(..)
                | AstOp::FpToFp(..)
                | AstOp::FpFP(..)
                | AstOp::BvToFp(..)
                | AstOp::BvToFpSigned(..)
                | AstOp::BvToFpUnsigned(..) => float::simplify_float(state),

                // String ops
                AstOp::StringS(..)
                | AstOp::StringV(..)
                | AstOp::StrConcat(..)
                | AstOp::StrSubstr(..)
                | AstOp::StrReplace(..)
                | AstOp::BVToStr(..) => string::simplify_string(state),

                // Cross-sort ops that need dispatch based on children
                AstOp::Not(child) => {
                    if child.op().base_theories().contains(Theories::BITVEC) {
                        bv::simplify_bv(state, error_on_dbz)
                    } else {
                        bool::simplify_bool(state)
                    }
                }

                AstOp::And(args) | AstOp::Or(args) | AstOp::Xor(args) => {
                    // Check first arg to determine if bool or bv
                    if let Some(first) = args.first() {
                        if first.op().base_theories().contains(Theories::BITVEC) {
                            bv::simplify_bv(state, error_on_dbz)
                        } else {
                            bool::simplify_bool(state)
                        }
                    } else {
                        bool::simplify_bool(state)
                    }
                }

                AstOp::Eq(..) | AstOp::Neq(..) => bool::simplify_bool(state),

                AstOp::If(_, then_, _) => {
                    // Dispatch based on the type of the then branch
                    let theories = then_.op().base_theories();
                    if theories.contains(Theories::BITVEC) {
                        bv::simplify_bv(state, error_on_dbz)
                    } else if theories.contains(Theories::FLOAT) {
                        float::simplify_float(state)
                    } else if theories.contains(Theories::STRING) {
                        string::simplify_string(state)
                    } else {
                        bool::simplify_bool(state)
                    }
                }
            }
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

        let has_blocking_annotations = state
            .expr
            .annotations()
            .iter()
            .any(|a| !a.eliminatable() && !a.relocatable());
        let should_simplify = !respect_annotations || !has_blocking_annotations;
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
                Err(SimplifyError::ReRun(new_ast)) => {
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
