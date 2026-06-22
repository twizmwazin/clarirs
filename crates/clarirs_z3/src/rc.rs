use std::ops::Deref;

use ::z3 as z3hl;
use clarirs_core::error::ClarirsError;
use z3_sys as z3;
use z3hl::ast::Ast as _;

use crate::{check_z3_error, z3_context};

// Used only by the `#[cfg(test)]` introspection/builder helpers below.
#[cfg(test)]
use crate::Z3_CONTEXT;
#[cfg(test)]
use std::ffi::CStr;

/// A reference-counted Z3 AST.
///
/// The lifetime/ref-counting is owned by the high-level `z3` crate's
/// [`z3hl::ast::Dynamic`] handle (`inc_ref`/`dec_ref` happen in its `Clone`/`Drop`).
/// We additionally cache the raw [`z3::Z3_ast`] pointer so the C-API call sites in
/// `astext`/`solver` can keep dereferencing an `RcAst` straight to a `Z3_ast`.
#[derive(Clone)]
pub struct RcAst {
    dynamic: z3hl::ast::Dynamic,
    raw: z3::Z3_ast,
}

impl RcAst {
    /// The high-level handle, e.g. for use with `z3::Solver`/`Model` APIs.
    pub fn dynamic(&self) -> &z3hl::ast::Dynamic {
        &self.dynamic
    }

    /// Downcasts to a high-level [`z3hl::ast::Bool`]. Panics if this AST is not
    /// boolean — only called on constraints, which are boolean by construction.
    pub fn as_bool(&self) -> z3hl::ast::Bool {
        self.dynamic.as_bool().expect("expected a boolean Z3 AST")
    }

    /// Wraps an already reference-managed raw AST into a [`Dynamic`] handle.
    fn from_raw(raw: z3::Z3_ast) -> Self {
        let ctx = z3_context();
        RcAst {
            dynamic: unsafe { z3hl::ast::Dynamic::wrap(&ctx, raw) },
            raw,
        }
    }

    /// Returns the `DeclKind` of this AST node (assumes it is an application).
    #[cfg(test)]
    pub fn decl_kind(&self) -> z3::DeclKind {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let app = z3::Z3_to_app(ctx, self.raw).unwrap();
            let decl = z3::Z3_get_app_decl(ctx, app).unwrap();
            z3::Z3_get_decl_kind(ctx, decl)
        })
    }

    /// Returns the number of arguments (assumes it is an application).
    #[cfg(test)]
    pub fn num_args(&self) -> u32 {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let app = z3::Z3_to_app(ctx, self.raw).unwrap();
            z3::Z3_get_app_num_args(ctx, app)
        })
    }

    /// Returns the argument at `index` as a new `RcAst`, or `None` if out of
    /// bounds or the node is not an application.
    #[cfg(test)]
    pub fn arg(&self, index: u32) -> Option<RcAst> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let ast_kind = z3::Z3_get_ast_kind(ctx, self.raw);
            if ast_kind != z3::AstKind::App {
                return None;
            }
            let app = z3::Z3_to_app(ctx, self.raw).unwrap();
            let num_args = z3::Z3_get_app_num_args(ctx, app);
            if index >= num_args {
                return None;
            }
            RcAst::try_from(z3::Z3_get_app_arg(ctx, app, index)).ok()
        })
    }

    /// Returns the symbol name if this is an uninterpreted constant, or `None`
    /// otherwise.
    #[cfg(test)]
    pub fn symbol_name(&self) -> Option<String> {
        Z3_CONTEXT.with(|&ctx| unsafe {
            if z3::Z3_get_ast_kind(ctx, self.raw) != z3::AstKind::App {
                return None;
            }
            let app = z3::Z3_to_app(ctx, self.raw).unwrap();
            let decl = z3::Z3_get_app_decl(ctx, app).unwrap();
            if z3::Z3_get_decl_kind(ctx, decl) != z3::DeclKind::Uninterpreted {
                return None;
            }
            let sym = z3::Z3_get_decl_name(ctx, decl).unwrap();
            let name = z3::Z3_get_symbol_string(ctx, sym);
            CStr::from_ptr(name).to_str().ok().map(|s| s.to_owned())
        })
    }

    /// Creates a Z3 boolean symbol.
    #[cfg(test)]
    pub fn mk_bool(name: &str) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(&z3hl::ast::Bool::new_const(
            name,
        )))
    }

    /// Creates a Z3 bitvector symbol.
    #[cfg(test)]
    pub fn mk_bv(name: &str, width: u32) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(&z3hl::ast::BV::new_const(
            name, width,
        )))
    }

    /// Creates a Z3 floating-point symbol. Z3's sbits includes the implicit
    /// leading bit, so `mantissa + 1` is passed.
    #[cfg(test)]
    pub fn mk_fp(name: &str, sort: clarirs_core::prelude::FSort) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(&z3hl::ast::Float::new_const(
            name,
            sort.exponent,
            sort.mantissa + 1,
        )))
    }

    /// Creates a Z3 bitvector numeral from a decimal string value and width.
    #[cfg(test)]
    pub fn mk_bv_val(value: &str, width: u32) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(
            &z3hl::ast::BV::from_str(width, value).expect("invalid bitvector numeral"),
        ))
    }

    /// Creates a Z3 floating-point numeral from an `f32`.
    #[cfg(test)]
    pub fn mk_fp_val_f32(value: f32) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(&z3hl::ast::Float::from_f32(
            value,
        )))
    }

    /// Creates a Z3 floating-point numeral from an `f64`.
    #[cfg(test)]
    pub fn mk_fp_val_f64(value: f64) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(&z3hl::ast::Float::from_f64(
            value,
        )))
    }

    /// Creates a Z3 rounding mode AST.
    #[cfg(test)]
    pub fn mk_fprm(rm: clarirs_core::prelude::FPRM) -> RcAst {
        use clarirs_core::prelude::FPRM;
        Z3_CONTEXT.with(|&ctx| unsafe {
            RcAst::try_from(match rm {
                FPRM::NearestTiesToEven => z3::Z3_mk_fpa_rne(ctx),
                FPRM::TowardPositive => z3::Z3_mk_fpa_rtp(ctx),
                FPRM::TowardNegative => z3::Z3_mk_fpa_rtn(ctx),
                FPRM::TowardZero => z3::Z3_mk_fpa_rtz(ctx),
                FPRM::NearestTiesToAway => z3::Z3_mk_fpa_rna(ctx),
            })
            .unwrap()
        })
    }

    /// Creates a Z3 string (sequence of chars) symbol.
    #[cfg(test)]
    pub fn mk_string(name: &str) -> RcAst {
        RcAst::from(z3hl::ast::Dynamic::from_ast(&z3hl::ast::String::new_const(
            name,
        )))
    }

    /// Creates a Z3 string constant (literal value).
    #[cfg(test)]
    pub fn mk_string_val(value: &str) -> RcAst {
        Z3_CONTEXT.with(|&ctx| unsafe {
            let c_val = std::ffi::CString::new(value).unwrap();
            RcAst::try_from(z3::Z3_mk_string(ctx, c_val.as_ptr())).unwrap()
        })
    }
}

impl From<&RcAst> for RcAst {
    fn from(val: &RcAst) -> Self {
        val.clone()
    }
}

impl From<z3hl::ast::Dynamic> for RcAst {
    fn from(dynamic: z3hl::ast::Dynamic) -> Self {
        let raw = dynamic.get_z3_ast();
        RcAst { dynamic, raw }
    }
}

impl TryFrom<z3::Z3_ast> for RcAst {
    type Error = ClarirsError;

    fn try_from(ast: z3::Z3_ast) -> Result<Self, Self::Error> {
        check_z3_error()?;
        Ok(RcAst::from_raw(ast))
    }
}

/// z3-sys returns `Option<Z3_ast>` from every AST-building call (`None` on a Z3
/// error, e.g. a sort mismatch). Accepting the `Option` here keeps the
/// `to_z3`/`from_z3` call sites and the `unop!`/`binop!`/`naryop!` macros
/// unchanged: a null result surfaces the underlying Z3 error message via
/// `check_z3_error`, falling back to a generic backend error.
impl TryFrom<Option<z3::Z3_ast>> for RcAst {
    type Error = ClarirsError;

    fn try_from(ast: Option<z3::Z3_ast>) -> Result<Self, Self::Error> {
        check_z3_error()?;
        let ast = ast.ok_or_else(|| {
            ClarirsError::BackendError("Z3", "Z3 returned a null AST".to_string())
        })?;
        RcAst::try_from(ast)
    }
}

impl Deref for RcAst {
    type Target = z3::Z3_ast;

    fn deref(&self) -> &Self::Target {
        &self.raw
    }
}
