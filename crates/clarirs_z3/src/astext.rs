use clarirs_core::{algorithms::walk_post_order, prelude::*};
use z3::ast::{Ast, Dynamic};

use crate::Z3_AST_CACHE;

fn child(children: &[Dynamic], index: usize) -> Result<&Dynamic, ClarirsError> {
    children
        .get(index)
        .ok_or_else(|| ClarirsError::InvalidArguments(format!("missing child at index {index}")))
}

pub(crate) trait DynamicExt {
    fn to_bool(&self) -> Result<z3::ast::Bool, ClarirsError>;
    fn to_bv(&self) -> Result<z3::ast::BV, ClarirsError>;
    fn to_float(&self) -> Result<z3::ast::Float, ClarirsError>;
    fn to_string_ast(&self) -> Result<z3::ast::String, ClarirsError>;
    fn to_int(&self) -> Result<z3::ast::Int, ClarirsError>;
    fn nth(&self, index: usize) -> Result<Dynamic, ClarirsError>;
    fn get_decl(&self) -> Result<z3::FuncDecl, ClarirsError>;
}

impl DynamicExt for Dynamic {
    fn to_bool(&self) -> Result<z3::ast::Bool, ClarirsError> {
        self.as_bool()
            .ok_or_else(|| ClarirsError::ConversionError("expected bool sort".into()))
    }

    fn to_bv(&self) -> Result<z3::ast::BV, ClarirsError> {
        self.as_bv()
            .ok_or_else(|| ClarirsError::ConversionError("expected bv sort".into()))
    }

    fn to_float(&self) -> Result<z3::ast::Float, ClarirsError> {
        self.as_float()
            .ok_or_else(|| ClarirsError::ConversionError("expected float sort".into()))
    }

    fn to_string_ast(&self) -> Result<z3::ast::String, ClarirsError> {
        self.as_string()
            .ok_or_else(|| ClarirsError::ConversionError("expected string sort".into()))
    }

    fn to_int(&self) -> Result<z3::ast::Int, ClarirsError> {
        self.as_int()
            .ok_or_else(|| ClarirsError::ConversionError("expected int sort".into()))
    }

    fn nth(&self, index: usize) -> Result<Dynamic, ClarirsError> {
        self.nth_child(index)
            .ok_or_else(|| ClarirsError::ConversionError(format!("missing child at index {index}")))
    }

    fn get_decl(&self) -> Result<z3::FuncDecl, ClarirsError> {
        self.safe_decl()
            .map_err(|_| ClarirsError::ConversionError("not an app".into()))
    }
}

mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;
#[cfg(test)]
mod test_float;
#[cfg(test)]
mod test_string;

pub(crate) trait AstExtZ3<'c>: HasContext<'c> + Simplify<'c> + Sized {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: Dynamic) -> Result<Self, ClarirsError>;

    fn simplify_z3(&self) -> Result<Self, ClarirsError> {
        let ast = self.simplify()?.to_z3()?;
        let simplified_ast = ast.simplify();
        Self::from_z3(self.context(), simplified_ast)
    }
}

impl<'c> AstExtZ3<'c> for BoolAst<'c> {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: Dynamic) -> Result<Self, ClarirsError> {
        bool::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for BitVecAst<'c> {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: Dynamic) -> Result<Self, ClarirsError> {
        bv::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for FloatAst<'c> {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: Dynamic) -> Result<Self, ClarirsError> {
        float::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for StringAst<'c> {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: Dynamic) -> Result<Self, ClarirsError> {
        string::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for DynAst<'c> {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError> {
        Z3_AST_CACHE.with(|cache| {
            walk_post_order(
                self.clone(),
                |node, children| match node {
                    DynAst::Boolean(ast) => bool::to_z3(&ast, children),
                    DynAst::BitVec(ast) => bv::to_z3(&ast, children),
                    DynAst::Float(ast) => float::to_z3(&ast, children),
                    DynAst::String(ast) => string::to_z3(&ast, children),
                },
                cache,
            )
        })
    }

    fn from_z3(ctx: &'c Context<'c>, ast: Dynamic) -> Result<Self, ClarirsError> {
        match ast.sort_kind() {
            z3::SortKind::Bool => Ok(DynAst::Boolean(BoolAst::from_z3(ctx, ast)?)),
            z3::SortKind::BV => Ok(DynAst::BitVec(BitVecAst::from_z3(ctx, ast)?)),
            z3::SortKind::FloatingPoint => Ok(DynAst::Float(FloatAst::from_z3(ctx, ast)?)),
            z3::SortKind::Seq => Ok(DynAst::String(StringAst::from_z3(ctx, ast)?)),
            _ => Err(ClarirsError::ConversionError(format!(
                "unknown sort kind: {:?}",
                ast.sort_kind()
            ))),
        }
    }
}
