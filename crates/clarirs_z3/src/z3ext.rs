//! Helpers for building and introspecting z3 [`Dynamic`] ASTs through the
//! `z3-sys` C API. The orphan rule prevents hanging these directly off the
//! foreign [`Dynamic`] type, so they live here as a free function plus an
//! extension trait.

use ::z3 as z3hl;
use clarirs_core::error::ClarirsError;
use z3_sys as z3;
use z3hl::ast::{Ast as _, Dynamic};

use crate::{check_z3_error, z3_context};

#[cfg(test)]
use crate::Z3_CONTEXT;

/// Wraps a raw AST produced by a `z3-sys` builder into a reference-counted
/// [`Dynamic`]. `None` (a null pointer) indicates a Z3 error such as a sort
/// mismatch; the underlying message is surfaced via [`check_z3_error`], falling
/// back to a generic backend error.
pub(crate) fn wrap_ast(ast: Option<z3::Z3_ast>) -> Result<Dynamic, ClarirsError> {
    check_z3_error()?;
    let ast =
        ast.ok_or_else(|| ClarirsError::BackendError("Z3", "Z3 returned a null AST".to_string()))?;
    Ok(unsafe { Dynamic::wrap(&z3_context(), ast) })
}

/// Crate-internal extensions on [`Dynamic`] for the parts of the Z3 API still
/// reached through `z3-sys`.
pub(crate) trait DynExt {
    /// The raw `Z3_ast` pointer, for passing to `z3-sys` functions.
    fn raw(&self) -> z3::Z3_ast;

    /// Downcasts to a [`z3hl::ast::Bool`]. Panics if this AST is not boolean —
    /// only called on constraints, which are boolean by construction.
    fn expect_bool(&self) -> z3hl::ast::Bool;

    /// The symbol name if this is an uninterpreted constant, else `None`.
    /// (Kept as a helper since it guards on the decl kind rather than being a
    /// plain forward to the high-level API.)
    #[cfg(test)]
    fn symbol_name(&self) -> Option<String>;
}

impl DynExt for Dynamic {
    fn raw(&self) -> z3::Z3_ast {
        self.get_z3_ast()
    }

    fn expect_bool(&self) -> z3hl::ast::Bool {
        self.as_bool().expect("expected a boolean Z3 AST")
    }

    #[cfg(test)]
    fn symbol_name(&self) -> Option<String> {
        let decl = self.safe_decl().ok()?;
        (decl.kind() == z3::DeclKind::Uninterpreted).then(|| decl.name())
    }
}

/// The symbol name of `ast`'s `index`-th child. Test assertion helper that keeps
/// the common `nth_child(i).symbol_name()` check on a single line.
#[cfg(test)]
pub(crate) fn arg_sym(ast: &Dynamic, index: usize) -> Option<String> {
    ast.nth_child(index).unwrap().symbol_name()
}

// Test-only constructors that build Z3 ASTs directly.
#[cfg(test)]
pub(crate) fn mk_bool(name: &str) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::Bool::new_const(name))
}

#[cfg(test)]
pub(crate) fn mk_bv(name: &str, width: u32) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::BV::new_const(name, width))
}

/// Z3's sbits includes the implicit leading bit, so `mantissa + 1` is passed.
#[cfg(test)]
pub(crate) fn mk_fp(name: &str, sort: clarirs_core::prelude::FSort) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::Float::new_const(
        name,
        sort.exponent,
        sort.mantissa + 1,
    ))
}

#[cfg(test)]
pub(crate) fn mk_bv_val(value: &str, width: u32) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::BV::from_str(width, value).expect("invalid bitvector numeral"))
}

#[cfg(test)]
pub(crate) fn mk_fp_val_f32(value: f32) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::Float::from_f32(value))
}

#[cfg(test)]
pub(crate) fn mk_fp_val_f64(value: f64) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::Float::from_f64(value))
}

#[cfg(test)]
pub(crate) fn mk_fprm(rm: clarirs_core::prelude::FPRM) -> Dynamic {
    use clarirs_core::prelude::FPRM;
    Z3_CONTEXT.with(|&ctx| unsafe {
        wrap_ast(match rm {
            FPRM::NearestTiesToEven => z3::Z3_mk_fpa_rne(ctx),
            FPRM::TowardPositive => z3::Z3_mk_fpa_rtp(ctx),
            FPRM::TowardNegative => z3::Z3_mk_fpa_rtn(ctx),
            FPRM::TowardZero => z3::Z3_mk_fpa_rtz(ctx),
            FPRM::NearestTiesToAway => z3::Z3_mk_fpa_rna(ctx),
        })
        .unwrap()
    })
}

#[cfg(test)]
pub(crate) fn mk_string(name: &str) -> Dynamic {
    Dynamic::from_ast(&z3hl::ast::String::new_const(name))
}

#[cfg(test)]
pub(crate) fn mk_string_val(value: &str) -> Dynamic {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let c_val = std::ffi::CString::new(value).unwrap();
        wrap_ast(z3::Z3_mk_string(ctx, c_val.as_ptr())).unwrap()
    })
}
