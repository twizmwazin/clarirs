use std::collections::HashMap;

use crate::{
    algorithms::{pre_order::walk_pre_order, reconstruct::reconstruct_node},
    prelude::*,
};

pub trait Replace<'c>: Sized {
    fn replace(&self, from: &AstRef<'c>, to: &AstRef<'c>) -> Result<Self, ClarirsError>;
    fn replace_many(&self, replacements: &HashMap<u64, AstRef<'c>>) -> Result<Self, ClarirsError>;
}

impl<'c> Replace<'c> for AstRef<'c> {
    fn replace(&self, from: &AstRef<'c>, to: &AstRef<'c>) -> Result<Self, ClarirsError> {
        if !from.op().check_same_sort(to.op()) {
            return Err(ClarirsError::TypeError(
                "Replace types must match!".to_string(),
            ));
        }

        let ctx = self.context();
        walk_pre_order(
            self.clone(),
            |ast| {
                if **ast == **from {
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
                if let Some(replacement) = replacements.get(&node.hash()) {
                    Ok(Some(replacement.clone()))
                } else {
                    Ok(None)
                }
            },
            |node, children| reconstruct_node(ctx, &node, children),
        )
    }
}
