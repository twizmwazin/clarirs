use crate::prelude::*;

macro_rules! uniop_support_trait {
    ($name:ident, $($impler:ty, $factory_func:ident),*) => {
        paste::paste! {
            pub trait [<Supports $name>]<'c>: Op<'c> + Sized {
                fn [< $name:lower >](factory: &'c impl AstFactory<'c>, ast: impl IntoOwned<AstRef<'c, Self>>) -> Result<AstRef<'c, Self>, ClarirsError>;
            }
        }

        $(
            paste::paste! {
                impl<'c> [<Supports $name>]<'c> for $impler {
                    fn [< $name:lower >](factory: &'c impl AstFactory<'c>, ast: impl IntoOwned<AstRef<'c, Self>>) -> Result<AstRef<'c, Self>, ClarirsError> {
                        factory.$factory_func(<$impler>::[< $name >](ast.into_owned()))
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
                fn [< $name:lower >](factory: &'c impl AstFactory<'c>, lhs: impl IntoOwned<AstRef<'c, Self>>, rhs: impl IntoOwned<AstRef<'c, Self>>) -> Result<AstRef<'c, Self>, ClarirsError>;
            }
        }

        $(
            paste::paste! {
                impl<'c> [<Supports $name>]<'c> for $impler {
                    fn [< $name:lower >](factory: &'c impl AstFactory<'c>, lhs: impl IntoOwned<AstRef<'c, Self>>, rhs: impl IntoOwned<AstRef<'c, Self>>) -> Result<AstRef<'c, Self>, ClarirsError> {
                        factory.$factory_func(<$impler>::[< $name >](lhs.into_owned(), rhs.into_owned()))
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

pub trait SupportsIf<'c>: Op<'c> + Sized {
    fn if_(
        factory: &'c impl AstFactory<'c>,
        cond: impl IntoOwned<BoolAst<'c>>,
        then: impl IntoOwned<AstRef<'c, Self>>,
        els: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<AstRef<'c, Self>, ClarirsError>;
}

macro_rules! impl_supports_if {
    ($($impler:ty, $factory_func:ident),*) => {
        $(
            impl<'c> SupportsIf<'c> for $impler {
                fn if_(factory: &'c impl AstFactory<'c>, cond: impl IntoOwned<BoolAst<'c>>, then: impl IntoOwned<AstRef<'c, Self>>, els: impl IntoOwned<AstRef<'c, Self>>) -> Result<AstRef<'c, Self>, ClarirsError> {
                    let then_owned = then.into_owned();
                    let els_owned = els.into_owned();
                    if !then_owned.check_same_sort(&els_owned) {
                        return Err(ClarirsError::TypeError(format!("Sort mismatch in if-then-else: {:?} and {:?}", then_owned, els_owned)));
                    }
                    factory.$factory_func(<$impler>::If(cond.into_owned(), then_owned, els_owned))
                }
            }
        )*
    };
}

impl_supports_if!(
    BooleanOp<'c>,
    make_bool,
    BitVecOp<'c>,
    make_bitvec,
    FloatOp<'c>,
    make_float,
    StringOp<'c>,
    make_string
);

pub trait SupportsAnnotate<'c>: Op<'c> + Sized {
    fn annotate(
        ast: impl IntoOwned<AstRef<'c, Self>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c, Self>, ClarirsError>;
}

impl<'c> SupportsAnnotate<'c> for BooleanOp<'c> {
    fn annotate(
        ast: impl IntoOwned<AstRef<'c, Self>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c, Self>, ClarirsError> {
        let ast_owned = ast.into_owned();
        let annotations = ast_owned
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        ast_owned
            .context()
            .make_bool_annotated(ast_owned.op().clone(), annotations)
    }
}

impl<'c> SupportsAnnotate<'c> for BitVecOp<'c> {
    fn annotate(
        ast: impl IntoOwned<AstRef<'c, Self>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c, Self>, ClarirsError> {
        let ast_owned = ast.into_owned();
        let annotations = ast_owned
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        ast_owned
            .context()
            .make_bitvec_annotated(ast_owned.op().clone(), annotations)
    }
}

impl<'c> SupportsAnnotate<'c> for FloatOp<'c> {
    fn annotate(
        ast: impl IntoOwned<AstRef<'c, Self>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c, Self>, ClarirsError> {
        let ast_owned = ast.into_owned();
        let annotations = ast_owned
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        ast_owned
            .context()
            .make_float_annotated(ast_owned.op().clone(), annotations)
    }
}

impl<'c> SupportsAnnotate<'c> for StringOp<'c> {
    fn annotate(
        ast: impl IntoOwned<AstRef<'c, Self>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c, Self>, ClarirsError> {
        let ast_owned = ast.into_owned();
        let annotations = ast_owned
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        ast_owned
            .context()
            .make_string_annotated(ast_owned.op().clone(), annotations)
    }
}

pub trait SupportsEq<'c>: Op<'c> + Sized {
    fn eq_(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError>;
}

impl<'c> SupportsEq<'c> for BooleanOp<'c> {
    fn eq_(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::BoolEq(lhs.into_owned(), rhs.into_owned()))
    }
}

impl<'c> SupportsEq<'c> for BitVecOp<'c> {
    fn eq_(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::Eq(lhs.into_owned(), rhs.into_owned()))
    }
}

impl<'c> SupportsEq<'c> for FloatOp<'c> {
    fn eq_(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::FpEq(lhs.into_owned(), rhs.into_owned()))
    }
}

impl<'c> SupportsEq<'c> for StringOp<'c> {
    fn eq_(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::StrEq(lhs.into_owned(), rhs.into_owned()))
    }
}

pub trait SupportsNeq<'c>: Op<'c> + Sized {
    fn neq(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError>;
}

impl<'c> SupportsNeq<'c> for BooleanOp<'c> {
    fn neq(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::BoolNeq(lhs.into_owned(), rhs.into_owned()))
    }
}

impl<'c> SupportsNeq<'c> for BitVecOp<'c> {
    fn neq(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::Neq(lhs.into_owned(), rhs.into_owned()))
    }
}

impl<'c> SupportsNeq<'c> for FloatOp<'c> {
    fn neq(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::FpNeq(lhs.into_owned(), rhs.into_owned()))
    }
}

impl<'c> SupportsNeq<'c> for StringOp<'c> {
    fn neq(
        factory: &'c impl AstFactory<'c>,
        lhs: impl IntoOwned<AstRef<'c, Self>>,
        rhs: impl IntoOwned<AstRef<'c, Self>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        factory.make_bool(BooleanOp::StrNeq(lhs.into_owned(), rhs.into_owned()))
    }
}
