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

    fn get_bool_simplified(&mut self, index: usize) -> Result<AstRef<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
    }

    fn get_bv_simplified(&mut self, index: usize) -> Result<AstRef<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
    }

    fn get_fp_simplified(&mut self, index: usize) -> Result<AstRef<'c>, SimplifyError<'c>> {
        self.get_child_simplified(index)
    }

    fn get_string_simplified(&mut self, index: usize) -> Result<AstRef<'c>, SimplifyError<'c>> {
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

    fn get_bool_available(&self, index: usize) -> Result<AstRef<'c>, ClarirsError> {
        Ok(self.get_child_available(index))
    }

    fn get_bv_available(&self, index: usize) -> Result<AstRef<'c>, ClarirsError> {
        Ok(self.get_child_available(index))
    }

    #[allow(dead_code)]
    fn get_fp_available(&self, index: usize) -> Result<AstRef<'c>, ClarirsError> {
        Ok(self.get_child_available(index))
    }

    #[allow(dead_code)]
    fn get_string_available(&self, index: usize) -> Result<AstRef<'c>, ClarirsError> {
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
        .get_or_insert(state.expr.hash(), || match expr.return_type() {
            AstType::Bool => bool::simplify_bool(state),
            AstType::BitVec(_) => bv::simplify_bv(state, error_on_dbz),
            AstType::Float(_) => float::simplify_float(state),
            AstType::String => string::simplify_string(state),
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
                        .annotate_dyn(&result, relocatable_annotations)?;

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
