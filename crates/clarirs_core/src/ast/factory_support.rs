use crate::prelude::*;

macro_rules! uniop_support_trait {
    ($name:ident, $($impler:ty, $factory_func:ident),*) => {
        paste::paste! {
            pub(crate) trait [<Supports $name>]<'c>: Op<'c> + Sized {
                fn [< $name:lower >](factory: &'c impl AstFactory<'c>, ast: &AstRef<'c, Self>) -> Result<AstRef<'c, Self>, ClarirsError>;
            }
        }

        $(
            paste::paste! {
                impl<'c> [<Supports $name>]<'c> for $impler {
                    fn [< $name:lower >](factory: &'c impl AstFactory<'c>, ast: &AstRef<'c, Self>) -> Result<AstRef<'c, Self>, ClarirsError> {
                        factory.$factory_func(<$impler>::[< $name >](ast.clone()))
                    }
                }
            }
        )*
    };
}

uniop_support_trait!(Not, BooleanOp<'c>, make_bool, BitVecOp<'c>, make_bitvec);

macro_rules! binop_support_trait {
    ($name:ident, $($impler:ty, $factory_func:ident),*) => {
        paste::paste! {
            pub trait [<Supports $name>]<'c>: Op<'c> + Sized {
                fn [< $name:lower >](factory: &'c impl AstFactory<'c>, lhs: &AstRef<'c, Self>, rhs: &AstRef<'c, Self>) -> Result<AstRef<'c, Self>, ClarirsError>;
            }
        }

        $(
            paste::paste! {
                impl<'c> [<Supports $name>]<'c> for $impler {
                    fn [< $name:lower >](factory: &'c impl AstFactory<'c>, lhs: &AstRef<'c, Self>, rhs: &AstRef<'c, Self>) -> Result<AstRef<'c, Self>, ClarirsError> {
                        factory.$factory_func(<$impler>::[< $name >](lhs.clone(), rhs.clone()))
                    }
                }
            }
        )*
    };
}

binop_support_trait!(And, BooleanOp<'c>, make_bool, BitVecOp<'c>, make_bitvec);
binop_support_trait!(Or, BooleanOp<'c>, make_bool, BitVecOp<'c>, make_bitvec);
binop_support_trait!(Xor, BooleanOp<'c>, make_bool, BitVecOp<'c>, make_bitvec);
binop_support_trait!(Add, BitVecOp<'c>, make_bitvec);
binop_support_trait!(Sub, BitVecOp<'c>, make_bitvec);
binop_support_trait!(Mul, BitVecOp<'c>, make_bitvec);
binop_support_trait!(UDiv, BitVecOp<'c>, make_bitvec);
binop_support_trait!(SDiv, BitVecOp<'c>, make_bitvec);
binop_support_trait!(URem, BitVecOp<'c>, make_bitvec);
binop_support_trait!(SRem, BitVecOp<'c>, make_bitvec);
binop_support_trait!(Pow, BitVecOp<'c>, make_bitvec);

pub trait SupportsIf<'c>: Op<'c> + Sized {
    fn if_(
        factory: &'c impl AstFactory<'c>,
        cond: &BoolAst<'c>,
        then: &AstRef<'c, Self>,
        els: &AstRef<'c, Self>,
    ) -> Result<AstRef<'c, Self>, ClarirsError>;
}

pub trait SupportsAnnotated<'c>: Op<'c> + Sized {
    fn annotated(
        factory: &'c impl AstFactory<'c>,
        ast: &AstRef<'c, Self>,
        annotation: Annotation,
    ) -> Result<AstRef<'c, Self>, ClarirsError>;
}

macro_rules! impl_supports_if_and_annotated {
    ($($impler:ty, $factory_func:ident),*) => {
        $(
            impl<'c> SupportsIf<'c> for $impler {
                fn if_(factory: &'c impl AstFactory<'c>, cond: &BoolAst<'c>, then: &AstRef<'c, Self>, els: &AstRef<'c, Self>) -> Result<AstRef<'c, Self>, ClarirsError> {
                    factory.$factory_func(<$impler>::If(cond.clone(), then.clone(), els.clone()))
                }
            }

            impl<'c> SupportsAnnotated<'c> for $impler {
                fn annotated(factory: &'c impl AstFactory<'c>, ast: &AstRef<'c, Self>, annotation: Annotation) -> Result<AstRef<'c, Self>, ClarirsError> {
                    factory.$factory_func(<$impler>::Annotated(ast.clone(), annotation))
                }
            }
        )*
    };
}

impl_supports_if_and_annotated!(
    BooleanOp<'c>,
    make_bool,
    BitVecOp<'c>,
    make_bitvec,
    FloatOp<'c>,
    make_float,
    StringOp<'c>,
    make_string
);
