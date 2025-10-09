use clarirs_core::algorithms::walk_post_order;
use clarirs_core::ast::MakeLike;
use clarirs_core::ast::annotation::AnnotationType;
use clarirs_core::prelude::*;

/// This un-normalizes the AST by converting SI back into annotated BVS.
pub trait Denormalize: Sized {
    fn denormalize(self) -> Result<Self, ClarirsError>;
}

impl Denormalize for DynAst<'_> {
    fn denormalize(self) -> Result<Self, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match &node {
                DynAst::BitVec(ast) => {
                    if let BitVecOp::SI(bits, stride, lower_bound, upper_bound) = ast.op() {
                        ast.context()
                            .annotate(
                                &ast.context().bvs(
                                    format!("SI{bits}[{stride} {lower_bound} {upper_bound}]"),
                                    *bits,
                                )?,
                                Annotation::new(
                                    AnnotationType::StridedInterval {
                                        stride: stride.clone(),
                                        lower_bound: lower_bound.clone(),
                                        upper_bound: upper_bound.clone(),
                                    },
                                    false,
                                    false,
                                ),
                            )
                            .map(DynAst::from)
                    } else {
                        node.make_like(children)
                    }
                }
                _ => node.make_like(children),
            },
            &(),
        )
    }
}

impl Denormalize for BoolAst<'_> {
    fn denormalize(self) -> Result<Self, ClarirsError> {
        DynAst::from(self).denormalize()?.into_bool().ok_or(
            ClarirsError::InvalidArgumentsWithMessage(
                "Failed to convert denormalized AST back to BoolAst".to_string(),
            ),
        )
    }
}

impl Denormalize for BitVecAst<'_> {
    fn denormalize(self) -> Result<Self, ClarirsError> {
        DynAst::from(self).denormalize()?.into_bitvec().ok_or(
            ClarirsError::InvalidArgumentsWithMessage(
                "Failed to convert denormalized AST back to BitVecAst".to_string(),
            ),
        )
    }
}

impl Denormalize for FloatAst<'_> {
    fn denormalize(self) -> Result<Self, ClarirsError> {
        DynAst::from(self).denormalize()?.into_float().ok_or(
            ClarirsError::InvalidArgumentsWithMessage(
                "Failed to convert denormalized AST back to FloatAst".to_string(),
            ),
        )
    }
}

impl Denormalize for StringAst<'_> {
    fn denormalize(self) -> Result<Self, ClarirsError> {
        DynAst::from(self).denormalize()?.into_string().ok_or(
            ClarirsError::InvalidArgumentsWithMessage(
                "Failed to convert denormalized AST back to StringAst".to_string(),
            ),
        )
    }
}
