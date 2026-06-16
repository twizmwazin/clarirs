//! Hooks for VSA-backed queries on AST wrapper classes.
//!
//! The `cardinality`/`singlevalued`/`multivalued` getters on `BV` and `Bool`
//! are computed via Value Set Analysis, which lives in the `clarirs-vsa` crate.
//! That crate depends on `clarirs_core`, so the bindings here cannot call it
//! directly without forming a dependency cycle. Instead, the `clarirs_py` crate
//! (which sits above both) installs these function pointers at module-init time,
//! and the getters dispatch through them.

use std::sync::OnceLock;

use num_bigint::BigUint;

use crate::prelude::*;

type BvCardinalityFn = fn(&AstRef<'static>) -> Result<BigUint, ClarirsError>;
type BoolCardinalityFn = fn(&AstRef<'static>) -> Result<usize, ClarirsError>;

pub static BV_CARDINALITY: OnceLock<BvCardinalityFn> = OnceLock::new();
pub static BOOL_CARDINALITY: OnceLock<BoolCardinalityFn> = OnceLock::new();

fn unavailable() -> ClarirsError {
    ClarirsError::UnsupportedOperation(
        "VSA support is not installed; cardinality queries are unavailable".to_string(),
    )
}

/// Cardinality of a bitvector expression, via the installed VSA hook.
pub fn bv_cardinality(ast: &AstRef<'static>) -> Result<BigUint, ClarirsError> {
    (BV_CARDINALITY.get().ok_or_else(unavailable)?)(ast)
}

/// Cardinality of a boolean expression (1 if definite, 2 if it may be either),
/// via the installed VSA hook.
pub fn bool_cardinality(ast: &AstRef<'static>) -> Result<usize, ClarirsError> {
    (BOOL_CARDINALITY.get().ok_or_else(unavailable)?)(ast)
}
