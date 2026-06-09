//! Boolean-flavored aliases over the unified [`AstOp`]/[`AstRef`].
//!
//! `BooleanOp` and `BoolAst` are aliases for the single op enum and node
//! reference; they are kept for readability and to preserve existing import
//! paths.

pub use super::node::BoolAst;
pub use super::op::AstOp as BooleanOp;
