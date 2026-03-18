use std::collections::HashMap;

use crate::{
    algorithms::{pre_order::walk_pre_order, reconstruct::reconstruct_node},
    prelude::*,
};

/// Replaces subexpressions in an AST according to a dictionary mapping AST hashes
/// to replacement ASTs. All replacements are applied in a single pre-order pass.
///
/// This is the multi-replacement counterpart of [`Replace`](super::Replace).
pub fn replace_dict<'c>(
    ast: &DynAst<'c>,
    replacements: &HashMap<u64, DynAst<'c>>,
) -> Result<DynAst<'c>, ClarirsError> {
    if replacements.is_empty() {
        return Ok(ast.clone());
    }

    let ctx = ast.context();
    walk_pre_order(
        ast.clone(),
        // pre_visit: short-circuit when a node has a known replacement
        |node| {
            if let Some(replacement) = replacements.get(&node.inner_hash()) {
                Ok(Some(replacement.clone()))
            } else {
                Ok(None)
            }
        },
        // post_visit: rebuild the node from transformed children
        |node, children| reconstruct_node(ctx, &node, children),
    )
}

/// Helper to apply a replacement dictionary to a `BoolAst`.
pub fn replace_dict_bool<'c>(
    ast: &BoolAst<'c>,
    replacements: &HashMap<u64, DynAst<'c>>,
) -> Result<BoolAst<'c>, ClarirsError> {
    replace_dict(&DynAst::Boolean(ast.clone()), replacements)?
        .into_bool()
        .ok_or(ClarirsError::TypeError(
            "Expected Boolean after replacement".to_string(),
        ))
}

/// Helper to apply a replacement dictionary to a `BitVecAst`.
pub fn replace_dict_bitvec<'c>(
    ast: &BitVecAst<'c>,
    replacements: &HashMap<u64, DynAst<'c>>,
) -> Result<BitVecAst<'c>, ClarirsError> {
    replace_dict(&DynAst::BitVec(ast.clone()), replacements)?
        .into_bitvec()
        .ok_or(ClarirsError::TypeError(
            "Expected BitVec after replacement".to_string(),
        ))
}

/// Helper to apply a replacement dictionary to a `FloatAst`.
pub fn replace_dict_float<'c>(
    ast: &FloatAst<'c>,
    replacements: &HashMap<u64, DynAst<'c>>,
) -> Result<FloatAst<'c>, ClarirsError> {
    replace_dict(&DynAst::Float(ast.clone()), replacements)?
        .into_float()
        .ok_or(ClarirsError::TypeError(
            "Expected Float after replacement".to_string(),
        ))
}

/// Helper to apply a replacement dictionary to a `StringAst`.
pub fn replace_dict_string<'c>(
    ast: &StringAst<'c>,
    replacements: &HashMap<u64, DynAst<'c>>,
) -> Result<StringAst<'c>, ClarirsError> {
    replace_dict(&DynAst::String(ast.clone()), replacements)?
        .into_string()
        .ok_or(ClarirsError::TypeError(
            "Expected String after replacement".to_string(),
        ))
}
