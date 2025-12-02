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
        self.simplify_ext(true)
    }

    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError>;
}

impl<'c> Simplify<'c> for BoolAst<'c> {
    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::Boolean(self.clone())
            .simplify_ext(respect_annotations)?
            .as_bool()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))
    }
}

impl<'c> Simplify<'c> for BitVecAst<'c> {
    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::BitVec(self.clone())
            .simplify_ext(respect_annotations)?
            .as_bitvec()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected BvAst".to_string()))
    }
}

impl<'c> Simplify<'c> for FloatAst<'c> {
    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::Float(self.clone())
            .simplify_ext(respect_annotations)?
            .as_float()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))
    }
}

impl<'c> Simplify<'c> for StringAst<'c> {
    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::String(self.clone())
            .simplify_ext(respect_annotations)?
            .as_string()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))
    }
}

impl<'c> Simplify<'c> for DynAst<'c> {
    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        simplify(self, respect_annotations)
    }
}

struct SimplifyState<'c> {
    expr: DynAst<'c>,
    children: [Option<DynAst<'c>>; 3], // No op has more than 3 ast children
    last_missed_child: Option<u8>,
}

impl<'c> SimplifyState<'c> {
    fn new(expr: DynAst<'c>) -> Self {
        Self {
            expr,
            children: [None, None, None],
            last_missed_child: None,
        }
    }

    fn get_child(&mut self, index: usize) -> Result<DynAst<'c>, ClarirsError> {
        if let Some(child) = &self.children[index] {
            Ok(child.clone())
        } else {
            self.last_missed_child = Some(index as u8);
            Err(ClarirsError::MissingChild(index))
        }
    }

    fn get_bool_child(&mut self, index: usize) -> Result<BoolAst<'c>, ClarirsError> {
        self.get_child(index)?
            .into_bool()
            .ok_or(ClarirsError::TypeError("Expected bool child".into()))
    }

    fn get_bv_child(&mut self, index: usize) -> Result<BitVecAst<'c>, ClarirsError> {
        self.get_child(index)?
            .into_bitvec()
            .ok_or(ClarirsError::TypeError("Expected bitvector child".into()))
    }

    fn get_fp_child(&mut self, index: usize) -> Result<FloatAst<'c>, ClarirsError> {
        self.get_child(index)?
            .into_float()
            .ok_or(ClarirsError::TypeError("Expected float child".into()))
    }

    fn get_string_child(&mut self, index: usize) -> Result<StringAst<'c>, ClarirsError> {
        self.get_child(index)?
            .into_string()
            .ok_or(ClarirsError::TypeError("Expected string child".into()))
    }
}

fn simplify_inner<'c>(state: &mut SimplifyState<'c>) -> Result<DynAst<'c>, ClarirsError> {
    let expr = &state.expr.clone();
    expr.context()
        .simplification_cache
        .get_or_insert(state.expr.inner_hash(), || match expr {
            DynAst::Boolean(_) => bool::simplify_bool(state).map(DynAst::Boolean),
            DynAst::BitVec(_) => bv::simplify_bv(state).map(DynAst::BitVec),
            DynAst::Float(_) => float::simplify_float(state).map(DynAst::Float),
            DynAst::String(_) => string::simplify_string(state).map(DynAst::String),
        })
}

fn simplify<'c>(ast: &DynAst<'c>, respect_annotations: bool) -> Result<DynAst<'c>, ClarirsError> {
    let mut work_stack: Vec<SimplifyState<'c>> = Vec::new();
    let mut last_result: Option<DynAst<'c>> = None;

    work_stack.push(SimplifyState::new(ast.clone()));

    while let Some(mut state) = work_stack.pop() {
        if let Some(missed_index) = state.last_missed_child {
            // We missed a child last time, so we need to get the last result and set it as the child
            state.children[missed_index as usize] = Some(last_result.take().unwrap());
            state.last_missed_child = None;
        }

        let should_simplify = !(respect_annotations
            && state
                .expr
                .annotations()
                .iter()
                .any(|a| !a.eliminatable() && !a.relocatable()));
        if should_simplify {
            let inner_result = simplify_inner(&mut state);
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
                    last_result = Some(annotated)
                }
                Err(ClarirsError::MissingChild(index)) => {
                    let child_state =
                        SimplifyState::new(state.expr.children().get(index).unwrap().clone());

                    // Push the current state back onto the stack
                    work_stack.push(state);
                    // Push the missing child onto the stack
                    work_stack.push(child_state);
                }
                Err(e) => {
                    return Err(e);
                }
            }
        } else {
            last_result = Some(state.expr.clone());
        }
    }

    if last_result.is_none() {
        return Err(ClarirsError::InvalidArgumentsWithMessage(
            "No result produced".to_string(),
        ));
    }

    Ok(last_result.unwrap())
}
