mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;

use std::collections::HashSet;

use crate::prelude::*;

pub fn extract_bool_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<BoolAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_bool())
        .ok_or(ClarirsError::InvalidArguments)
}

pub fn extract_bitvec_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<BitVecAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_bitvec())
        .ok_or(ClarirsError::InvalidArguments)
}

pub fn extract_float_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<FloatAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_float())
        .ok_or(ClarirsError::InvalidArguments)
}

pub fn extract_string_child<'c>(
    children: &[DynAst<'c>],
    index: usize,
) -> Result<StringAst<'c>, ClarirsError> {
    children
        .get(index)
        .and_then(|child| child.clone().into_string())
        .ok_or(ClarirsError::InvalidArguments)
}

use super::walk_post_order;

pub trait Simplify<'c>: Sized {
    fn simplify(&self) -> Result<Self, ClarirsError>;
    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError>;
}

impl<'c> Simplify<'c> for BoolAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        self.simplify_ext(true)
    }

    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::Boolean(self.clone())
            .simplify_ext(respect_annotations)?
            .as_bool()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))
    }
}

impl<'c> Simplify<'c> for BitVecAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        self.simplify_ext(true)
    }

    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::BitVec(self.clone())
            .simplify_ext(respect_annotations)?
            .as_bitvec()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected BvAst".to_string()))
    }
}

impl<'c> Simplify<'c> for FloatAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        self.simplify_ext(true)
    }

    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::Float(self.clone())
            .simplify_ext(respect_annotations)?
            .as_float()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))
    }
}

impl<'c> Simplify<'c> for StringAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        self.simplify_ext(true)
    }

    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        DynAst::String(self.clone())
            .simplify_ext(respect_annotations)?
            .as_string()
            .cloned()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))
    }
}

impl<'c> Simplify<'c> for DynAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        self.simplify_ext(true)
    }

    fn simplify_ext(&self, respect_annotations: bool) -> Result<Self, ClarirsError> {
        // When respect_annotations is false, we don't use the cache to avoid
        // returning cached results that respected annotations
        if respect_annotations {
            walk_post_order(
                self.clone(),
                |node, children| {
                    if node
                        .annotations()
                        .iter()
                        .any(|a| !a.eliminatable() && !a.relocatable())
                    {
                        Ok(node)
                    } else {
                        let relocatable_annos: HashSet<Annotation> = HashSet::from_iter(
                            node.annotations()
                                .iter()
                                .filter(|a| !a.eliminatable() && a.relocatable())
                                .cloned(),
                        );
                        match node {
                            DynAst::Boolean(ast) => bool::simplify_bool(&ast, children)
                                .and_then(|ast| {
                                    ast.context()
                                        .make_bool_annotated(ast.op().clone(), relocatable_annos)
                                })
                                .map(DynAst::Boolean),
                            DynAst::BitVec(ast) => bv::simplify_bv(&ast, children)
                                .and_then(|ast| {
                                    ast.context()
                                        .make_bitvec_annotated(ast.op().clone(), relocatable_annos)
                                })
                                .map(DynAst::BitVec),
                            DynAst::Float(ast) => float::simplify_float(&ast, children)
                                .and_then(|ast| {
                                    ast.context()
                                        .make_float_annotated(ast.op().clone(), relocatable_annos)
                                })
                                .map(DynAst::Float),
                            DynAst::String(ast) => string::simplify_string(&ast, children)
                                .and_then(|ast| {
                                    ast.context()
                                        .make_string_annotated(ast.op().clone(), relocatable_annos)
                                })
                                .map(DynAst::String),
                        }
                    }
                },
                &self.context().simplification_cache,
            )
        } else {
            walk_post_order(
                self.clone(),
                |node, children| {
                    let relocatable_annos: HashSet<Annotation> = HashSet::from_iter(
                        node.annotations()
                            .iter()
                            .filter(|a| !a.eliminatable() && a.relocatable())
                            .cloned(),
                    );
                    match node {
                        DynAst::Boolean(ast) => bool::simplify_bool(&ast, children)
                            .and_then(|ast| {
                                ast.context()
                                    .make_bool_annotated(ast.op().clone(), relocatable_annos)
                            })
                            .map(DynAst::Boolean),
                        DynAst::BitVec(ast) => bv::simplify_bv(&ast, children)
                            .and_then(|ast| {
                                ast.context()
                                    .make_bitvec_annotated(ast.op().clone(), relocatable_annos)
                            })
                            .map(DynAst::BitVec),
                        DynAst::Float(ast) => float::simplify_float(&ast, children)
                            .and_then(|ast| {
                                ast.context()
                                    .make_float_annotated(ast.op().clone(), relocatable_annos)
                            })
                            .map(DynAst::Float),
                        DynAst::String(ast) => string::simplify_string(&ast, children)
                            .and_then(|ast| {
                                ast.context()
                                    .make_string_annotated(ast.op().clone(), relocatable_annos)
                            })
                            .map(DynAst::String),
                    }
                },
                &(),
            )
        }
    }
}
