use crate::prelude::*;

pub trait Join<'c> {
    fn and_join(self, ctx: &'c Context<'c>) -> Result<AstRef<'c>, ClarirsError>;
    fn or_join(self, ctx: &'c Context<'c>) -> Result<AstRef<'c>, ClarirsError>;
}

impl<'c, T: IntoIterator<Item = AstRef<'c>>> Join<'c> for T {
    fn and_join(self, ctx: &'c Context<'c>) -> Result<AstRef<'c>, ClarirsError> {
        and_join(ctx, self)
    }

    fn or_join(self, ctx: &'c Context<'c>) -> Result<AstRef<'c>, ClarirsError> {
        or_join(ctx, self)
    }
}

pub fn and_join<'c, I>(ctx: &'c Context<'c>, asts: I) -> Result<AstRef<'c>, ClarirsError>
where
    I: IntoIterator<Item = AstRef<'c>>,
{
    let mut result = ctx.true_()?;
    for ast in asts.into_iter() {
        if ast.is_false() {
            return ctx.false_();
        }
        result = ctx.and(&result, &ast)?;
    }
    Ok(result)
}

pub fn or_join<'c, I>(ctx: &'c Context<'c>, asts: I) -> Result<AstRef<'c>, ClarirsError>
where
    I: IntoIterator<Item = AstRef<'c>>,
{
    let mut result = ctx.false_()?;
    for ast in asts.into_iter() {
        if ast.is_true() {
            return ctx.true_();
        }
        result = ctx.or(&result, &ast)?;
    }
    Ok(result)
}
