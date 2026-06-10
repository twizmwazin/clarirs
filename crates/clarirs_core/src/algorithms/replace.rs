use std::collections::HashMap;
use std::mem::discriminant;

use crate::{
    algorithms::{pre_order::walk_pre_order, reconstruct::reconstruct_node},
    prelude::*,
};

pub trait Replace<'c>: Sized {
    fn replace<T: Clone + Into<AstRef<'c>>>(&self, from: &T, to: &T) -> Result<Self, ClarirsError>;
    fn replace_many(&self, replacements: &HashMap<u64, AstRef<'c>>) -> Result<Self, ClarirsError>;
}

impl<'c> Replace<'c> for AstRef<'c> {
    fn replace<T: Clone + Into<AstRef<'c>>>(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        let from = from.clone().into();
        let to = to.clone().into();

        if discriminant(&from.ty()) != discriminant(&to.ty()) {
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
            |ast| {
                if *ast == from {
                    Ok(Some(to.clone()))
                } else {
                    Ok(None)
                }
            },
            |ast, children| reconstruct_node(ctx, &ast, children),
        )
    }

    fn replace_many(&self, replacements: &HashMap<u64, AstRef<'c>>) -> Result<Self, ClarirsError> {
        if replacements.is_empty() {
            return Ok(self.clone());
        }

        let ctx = self.context();
        walk_pre_order(
            self.clone(),
            |node| {
                if let Some(replacement) = replacements.get(&node.inner_hash()) {
                    Ok(Some(replacement.clone()))
                } else {
                    Ok(None)
                }
            },
            |node, children| reconstruct_node(ctx, &node, children),
        )
    }
}
