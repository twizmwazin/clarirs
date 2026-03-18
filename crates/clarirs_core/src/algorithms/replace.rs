use std::mem::discriminant;

use crate::{
    algorithms::{pre_order::walk_pre_order, reconstruct::reconstruct_node},
    ast::{bitvec::BitVecOpExt, float::FloatOpExt},
    prelude::*,
};

pub trait Replace<'c, T>: Sized {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError>;
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for DynAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        let from = from.clone().into();
        let to = to.clone().into();

        if discriminant(&from) != discriminant(&to) {
            return Err(ClarirsError::TypeError(
                "Replace types must match!".to_string(),
            ));
        }
        if let Some(from_bv) = from.as_bitvec()
            && let Some(to_bv) = to.as_bitvec()
            && from_bv.size() != to_bv.size()
        {
            return Err(ClarirsError::TypeError(
                "BitVec sizes must match for replacement!".to_string(),
            ));
        }
        if let Some(from_fp) = from.as_float()
            && let Some(to_fp) = to.as_float()
            && from_fp.sort() != to_fp.sort()
        {
            return Err(ClarirsError::TypeError(
                "Float sorts must match for replacement!".to_string(),
            ));
        }

        let ctx = self.context();
        walk_pre_order(
            self.clone(),
            // pre_visit: short-circuit when a node matches `from`
            |ast| {
                if *ast == from {
                    Ok(Some(to.clone()))
                } else {
                    Ok(None)
                }
            },
            // post_visit: rebuild the node from transformed children
            |ast, children| reconstruct_node(ctx, &ast, children),
        )
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for BoolAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::Boolean(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_bool().ok_or(ClarirsError::TypeError(
                    "Expected Boolean after replacement".to_string(),
                ))
            })
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for BitVecAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::BitVec(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_bitvec().ok_or(ClarirsError::TypeError(
                    "Expected BitVec after replacement".to_string(),
                ))
            })
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for FloatAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::Float(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_float().ok_or(ClarirsError::TypeError(
                    "Expected Float after replacement".to_string(),
                ))
            })
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for StringAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::String(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_string().ok_or(ClarirsError::TypeError(
                    "Expected String after replacement".to_string(),
                ))
            })
    }
}
