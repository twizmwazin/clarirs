//! String-flavored aliases over the unified [`AstOp`]/[`AstRef`].
//!
//! `StringOp` and `StringAst` are aliases for the single op enum and node
//! reference; they are kept for readability and to preserve existing import
//! paths.

pub use super::node::StringAst;
pub use super::op::AstOp as StringOp;
