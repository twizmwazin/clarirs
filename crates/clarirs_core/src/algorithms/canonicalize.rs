#![allow(clippy::mutable_key_type)]

use std::collections::HashMap;

use crate::{ast::bitvec::BitVecOpExt, ast::float::FloatOpExt, prelude::*};

use super::{collect_vars::collect_vars, replace::Replace};

/// Checks if two ASTs are structurally matching by comparing their canonical forms.
///
/// Two ASTs are considered structurally matching if they have the same structure
/// and operations, even if their variable names are different.
///
/// # Example
/// ```
/// use clarirs_core::prelude::*;
/// use clarirs_core::algorithms::canonicalize::structurally_match;
///
/// let ctx = Context::new();
/// let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
/// let ast2 = ctx.add(&ctx.bvs("a", 64)?, &ctx.bvs("b", 64)?)?;
///
/// assert!(structurally_match(&DynAst::from(&ast1), &DynAst::from(&ast2))?);
/// # Ok::<(), ClarirsError>(())
/// ```
pub fn structurally_match<'c>(ast1: &DynAst<'c>, ast2: &DynAst<'c>) -> Result<bool, ClarirsError> {
    let (_, _, canonical1) = canonicalize(ast1)?;
    let (_, _, canonical2) = canonicalize(ast2)?;
    Ok(canonical1 == canonical2)
}

/// Creates a canonical version of an AST by replacing variable names with
/// deterministic ones (v0, v1, v2, ...). This allows comparing two ASTs for
/// structural equality even if they have different variable names.
///
/// The function returns a tuple of the variable replacement map, the next
/// available canonical index, and the canonicalized AST. The replacement map is
/// keyed by each variable's hash and stores the canonical variable AST.
///
/// Variables are renamed in lexicographic order of their original names.
///
/// # Example
/// ```
/// use clarirs_core::prelude::*;
/// use clarirs_core::algorithms::canonicalize::canonicalize;
///
/// let ctx = Context::new();
/// let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
/// let ast2 = ctx.add(&ctx.bvs("a", 64)?, &ctx.bvs("b", 64)?)?;
///
/// let (_, _, canonical1) = canonicalize(&DynAst::from(&ast1))?;
/// let (_, _, canonical2) = canonicalize(&DynAst::from(&ast2))?;
///
/// // Both should be structurally identical after canonicalization
/// assert_eq!(canonical1, canonical2);
/// # Ok::<(), ClarirsError>(())
/// ```
pub fn canonicalize<'c>(
    ast: &DynAst<'c>,
) -> Result<(HashMap<u64, DynAst<'c>>, usize, DynAst<'c>), ClarirsError> {
    // Collect all variables in the AST
    let vars = collect_vars(ast)?;

    if vars.is_empty() {
        // No variables, return the original AST
        return Ok((HashMap::new(), 0, ast.clone()));
    }

    // Sort variable names to ensure deterministic ordering
    let mut var_names: Vec<String> = vars
        .iter()
        .flat_map(|v| v.variables().into_iter())
        .collect();
    var_names.sort();
    var_names.dedup();

    // Create mapping from original names to canonical names
    let var_mapping: HashMap<String, String> = var_names
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), format!("v{i}")))
        .collect();

    // Build replacement map: original var AST -> canonical var AST
    let mut replacements: HashMap<DynAst<'c>, DynAst<'c>> = HashMap::new();
    let mut replacement_map: HashMap<u64, DynAst<'c>> = HashMap::new();
    let ctx = ast.context();

    for var in vars {
        let var_names_set = var.variables();
        // Each variable should have exactly one name since we collected leaf variables
        if let Some(original_name) = var_names_set.iter().next() {
            if let Some(canonical_name) = var_mapping.get(original_name) {
                // Create the canonical variable with the same type and size as the original
                let canonical_var = match &var {
                    DynAst::Boolean(_) => DynAst::Boolean(ctx.bools(canonical_name)?),
                    DynAst::BitVec(bv) => {
                        let size = bv.size();
                        DynAst::BitVec(ctx.bvs(canonical_name, size)?)
                    }
                    DynAst::Float(fp) => {
                        let sort = fp.sort();
                        DynAst::Float(ctx.fps(canonical_name, sort)?)
                    }
                    DynAst::String(_) => DynAst::String(ctx.strings(canonical_name)?),
                };
                replacement_map.insert(var.inner_hash(), canonical_var.clone());
                replacements.insert(var.clone(), canonical_var);
            }
        }
    }

    // Apply all replacements to the AST
    let mut result = ast.clone();
    for (from, to) in replacements {
        result = replace_dyn(&result, &from, &to)?;
    }

    let counter = var_mapping.len();

    Ok((replacement_map, counter, result))
}

/// Helper function to replace a DynAst with another DynAst in a DynAst tree
fn replace_dyn<'c>(
    ast: &DynAst<'c>,
    from: &DynAst<'c>,
    to: &DynAst<'c>,
) -> Result<DynAst<'c>, ClarirsError> {
    if ast == from {
        return Ok(to.clone());
    }

    match (ast, to) {
        (DynAst::Boolean(ast_bool), DynAst::Boolean(to_bool)) => {
            if let DynAst::Boolean(from_bool) = from {
                Ok(DynAst::Boolean(ast_bool.replace(from_bool, to_bool)?))
            } else {
                Ok(ast.clone())
            }
        }
        (DynAst::BitVec(ast_bv), DynAst::BitVec(to_bv)) => {
            if let DynAst::BitVec(from_bv) = from {
                Ok(DynAst::BitVec(ast_bv.replace(from_bv, to_bv)?))
            } else {
                Ok(ast.clone())
            }
        }
        (DynAst::Float(ast_fp), DynAst::Float(to_fp)) => {
            if let DynAst::Float(from_fp) = from {
                Ok(DynAst::Float(ast_fp.replace(from_fp, to_fp)?))
            } else {
                Ok(ast.clone())
            }
        }
        (DynAst::String(ast_str), DynAst::String(to_str)) => {
            if let DynAst::String(from_str) = from {
                Ok(DynAst::String(ast_str.replace(from_str, to_str)?))
            } else {
                Ok(ast.clone())
            }
        }
        _ => {
            // Type mismatch, can't replace
            Ok(ast.clone())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_canonicalize_bitvec() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create two structurally identical ASTs with different variable names
        let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
        let ast2 = ctx.add(&ctx.bvs("a", 64)?, &ctx.bvs("b", 64)?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        let (map1, counter1, canonical1) = canonicalize(&dyn_ast1)?;
        let (map2, counter2, canonical2) = canonicalize(&dyn_ast2)?;

        // Both should be structurally identical after canonicalization
        assert_eq!(canonical1, canonical2);
        assert_eq!(counter1, counter2);
        assert_eq!(map1.len(), counter1);
        assert_eq!(map2.len(), counter2);

        Ok(())
    }

    #[test]
    fn test_canonicalize_bool() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create two structurally identical boolean ASTs with different variable names
        let ast1 = ctx.and(&ctx.bools("p")?, &ctx.bools("q")?)?;
        let ast2 = ctx.and(&ctx.bools("x")?, &ctx.bools("y")?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        let (map1, counter1, canonical1) = canonicalize(&dyn_ast1)?;
        let (map2, counter2, canonical2) = canonicalize(&dyn_ast2)?;

        assert_eq!(canonical1, canonical2);
        assert_eq!(counter1, counter2);
        assert_eq!(map1.len(), counter1);
        assert_eq!(map2.len(), counter2);

        Ok(())
    }

    #[test]
    fn test_canonicalize_complex() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create more complex ASTs with the same structure
        // Both should have the same variable names in the same positions
        let x1 = ctx.bvs("a", 32)?;
        let y1 = ctx.bvs("b", 32)?;
        let z1 = ctx.bvs("c", 32)?;
        let ast1 = ctx.add(&ctx.mul(&x1, &y1)?, &z1)?;

        let x2 = ctx.bvs("x", 32)?;
        let y2 = ctx.bvs("y", 32)?;
        let z2 = ctx.bvs("z", 32)?;
        let ast2 = ctx.add(&ctx.mul(&x2, &y2)?, &z2)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        let (_, counter1, canonical1) = canonicalize(&dyn_ast1)?;
        let (_, counter2, canonical2) = canonicalize(&dyn_ast2)?;

        // Both should canonicalize to: (v0 * v1) + v2
        assert_eq!(canonical1, canonical2);
        assert_eq!(counter1, counter2);

        Ok(())
    }

    #[test]
    fn test_canonicalize_no_vars() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create AST with no variables
        let ast = ctx.add(
            &ctx.bvv_prim_with_size(5u64, 32)?,
            &ctx.bvv_prim_with_size(10u64, 32)?,
        )?;
        let dyn_ast = DynAst::from(&ast);

        let (map, counter, canonical) = canonicalize(&dyn_ast)?;

        // Should be unchanged
        assert_eq!(dyn_ast, canonical);
        assert!(map.is_empty());
        assert_eq!(counter, 0);

        Ok(())
    }

    #[test]
    fn test_canonicalize_single_var() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let ast = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvv_prim_with_size(5u64, 64)?)?;
        let dyn_ast = DynAst::from(&ast);

        let (map, counter, canonical) = canonicalize(&dyn_ast)?;

        // Check that the variable was renamed to v0
        let canonical_expected =
            ctx.add(&ctx.bvs("v0", 64)?, &ctx.bvv_prim_with_size(5u64, 64)?)?;
        let dyn_canonical_expected = DynAst::from(&canonical_expected);

        assert_eq!(canonical, dyn_canonical_expected);
        assert_eq!(map.len(), 1);
        assert_eq!(counter, 1);

        Ok(())
    }

    #[test]
    fn test_canonicalize_order_independence() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Test that variables are renamed in lexicographic order
        // regardless of their order in the AST
        let ast1 = ctx.add(&ctx.bvs("z", 64)?, &ctx.bvs("a", 64)?)?;
        let ast2 = ctx.add(&ctx.bvs("a", 64)?, &ctx.bvs("z", 64)?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        let (_, counter1, canonical1) = canonicalize(&dyn_ast1)?;
        let (_, counter2, canonical2) = canonicalize(&dyn_ast2)?;

        // Both should canonicalize but may not be equal due to order
        // a -> v0, z -> v1
        let expected1 = ctx.add(&ctx.bvs("v1", 64)?, &ctx.bvs("v0", 64)?)?;
        let dyn_expected1 = DynAst::from(&expected1);

        let expected2 = ctx.add(&ctx.bvs("v0", 64)?, &ctx.bvs("v1", 64)?)?;
        let dyn_expected2 = DynAst::from(&expected2);

        assert_eq!(canonical1, dyn_expected1);
        assert_eq!(canonical2, dyn_expected2);
        assert_eq!(counter1, 2);
        assert_eq!(counter2, 2);

        Ok(())
    }

    // Tests for structurally_match function

    #[test]
    fn test_structurally_match_basic() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create two structurally identical ASTs with different variable names
        let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
        let ast2 = ctx.add(&ctx.bvs("a", 64)?, &ctx.bvs("b", 64)?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        assert!(structurally_match(&dyn_ast1, &dyn_ast2)?);

        Ok(())
    }

    #[test]
    fn test_structurally_match_different_ops() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create two ASTs with different operations
        let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
        let ast2 = ctx.mul(&ctx.bvs("a", 64)?, &ctx.bvs("b", 64)?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        assert!(!structurally_match(&dyn_ast1, &dyn_ast2)?);

        Ok(())
    }

    #[test]
    fn test_structurally_match_different_sizes() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create two ASTs with different bitvector sizes
        let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
        let ast2 = ctx.add(&ctx.bvs("a", 32)?, &ctx.bvs("b", 32)?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        assert!(!structurally_match(&dyn_ast1, &dyn_ast2)?);

        Ok(())
    }

    #[test]
    fn test_structurally_match_complex() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create complex nested ASTs with different variable names
        let x1 = ctx.bvs("p", 32)?;
        let y1 = ctx.bvs("q", 32)?;
        let z1 = ctx.bvs("r", 32)?;
        let ast1 = ctx.mul(&ctx.add(&x1, &y1)?, &z1)?;

        let x2 = ctx.bvs("alpha", 32)?;
        let y2 = ctx.bvs("beta", 32)?;
        let z2 = ctx.bvs("gamma", 32)?;
        let ast2 = ctx.mul(&ctx.add(&x2, &y2)?, &z2)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        assert!(structurally_match(&dyn_ast1, &dyn_ast2)?);

        Ok(())
    }

    #[test]
    fn test_structurally_match_boolean() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create two structurally identical boolean ASTs with different variable names
        let ast1 = ctx.or(
            &ctx.and(&ctx.bools("a")?, &ctx.bools("b")?)?,
            &ctx.bools("c")?,
        )?;
        let ast2 = ctx.or(
            &ctx.and(&ctx.bools("x")?, &ctx.bools("y")?)?,
            &ctx.bools("z")?,
        )?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);

        assert!(structurally_match(&dyn_ast1, &dyn_ast2)?);

        Ok(())
    }

    #[test]
    fn test_structurally_match_same_ast() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Same AST should match with itself
        let ast = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvs("y", 64)?)?;
        let dyn_ast = DynAst::from(&ast);

        assert!(structurally_match(&dyn_ast, &dyn_ast)?);

        Ok(())
    }

    #[test]
    fn test_structurally_match_constants() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // ASTs with constants and variables
        let ast1 = ctx.add(&ctx.bvs("x", 64)?, &ctx.bvv_prim_with_size(5u64, 64)?)?;
        let ast2 = ctx.add(&ctx.bvs("y", 64)?, &ctx.bvv_prim_with_size(5u64, 64)?)?;
        let ast3 = ctx.add(&ctx.bvs("z", 64)?, &ctx.bvv_prim_with_size(10u64, 64)?)?;

        let dyn_ast1 = DynAst::from(&ast1);
        let dyn_ast2 = DynAst::from(&ast2);
        let dyn_ast3 = DynAst::from(&ast3);

        // Same constant values should match
        assert!(structurally_match(&dyn_ast1, &dyn_ast2)?);
        // Different constant values should not match
        assert!(!structurally_match(&dyn_ast1, &dyn_ast3)?);

        Ok(())
    }
}
