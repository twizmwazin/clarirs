//! Compatibility shim providing short names for `z3-sys` symbols.
//!
//! In z3-sys, all Z3 object types are `NonNull<_Z3_xxx>` and creation
//! functions return `Option<NonNull<...>>`.  The wrapper functions here
//! unwrap the `Option` so that call-sites look the same as with the
//! former `clarirs-z3-sys` crate.

#![allow(clippy::too_many_arguments, clippy::missing_safety_doc)]

use std::ffi::c_uint;

// ── Type aliases ─────────────────────────────────────────────────────
pub type Context = z3_sys::Z3_context;
pub type Ast = z3_sys::Z3_ast;
pub type Sort = z3_sys::Z3_sort;
pub type FuncDecl = z3_sys::Z3_func_decl;
pub type App = z3_sys::Z3_app;
pub type Symbol = z3_sys::Z3_symbol;
pub type Params = z3_sys::Z3_params;
pub type Solver = z3_sys::Z3_solver;
pub type Model = z3_sys::Z3_model;
pub type Optimize = z3_sys::Z3_optimize;
pub type AstVector = z3_sys::Z3_ast_vector;
pub type Config = z3_sys::Z3_config;

// ── Enum re-exports ──────────────────────────────────────────────────
pub use z3_sys::AstKind;
pub use z3_sys::DeclKind;
pub use z3_sys::ErrorCode;
pub use z3_sys::SortKind;

// ── Lbool ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lbool {
    True,
    False,
    Undef,
}

impl From<z3_sys::Z3_lbool> for Lbool {
    fn from(val: z3_sys::Z3_lbool) -> Self {
        match val {
            z3_sys::Z3_L_TRUE => Lbool::True,
            z3_sys::Z3_L_FALSE => Lbool::False,
            _ => Lbool::Undef,
        }
    }
}

// ── Helpers ──────────────────────────────────────────────────────────

/// Unwrap an `Option` returned by a z3-sys function, panicking with a
/// descriptive message when Z3 unexpectedly returns a null pointer.
#[inline]
fn unwrap_z3<T>(opt: Option<T>, fn_name: &str) -> T {
    opt.unwrap_or_else(|| panic!("{fn_name} returned null"))
}

// ── Context management ───────────────────────────────────────────────

#[inline]
pub unsafe fn mk_config() -> Config {
    unwrap_z3(unsafe { z3_sys::Z3_mk_config() }, "Z3_mk_config")
}

#[inline]
pub unsafe fn mk_context(c: Config) -> Context {
    unwrap_z3(unsafe { z3_sys::Z3_mk_context(c) }, "Z3_mk_context")
}

pub use z3_sys::Z3_del_config as del_config;
pub use z3_sys::Z3_del_context as del_context;
pub use z3_sys::Z3_set_error_handler as set_error_handler;

// ── Error handling ───────────────────────────────────────────────────
pub use z3_sys::Z3_get_error_code as get_error_code;
pub use z3_sys::Z3_get_error_msg as get_error_msg;

// ── Symbols ──────────────────────────────────────────────────────────

#[inline]
pub unsafe fn mk_string_symbol(c: Context, s: z3_sys::Z3_string) -> Symbol {
    unwrap_z3(unsafe { z3_sys::Z3_mk_string_symbol(c, s) }, "Z3_mk_string_symbol")
}

// ── Sorts ────────────────────────────────────────────────────────────

#[inline]
pub unsafe fn mk_bool_sort(c: Context) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bool_sort(c) }, "Z3_mk_bool_sort")
}

#[inline]
pub unsafe fn mk_int_sort(c: Context) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_mk_int_sort(c) }, "Z3_mk_int_sort")
}

#[inline]
pub unsafe fn mk_bv_sort(c: Context, sz: c_uint) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bv_sort(c, sz) }, "Z3_mk_bv_sort")
}

#[inline]
pub unsafe fn mk_fpa_sort(c: Context, ebits: c_uint, sbits: c_uint) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_sort(c, ebits, sbits) }, "Z3_mk_fpa_sort")
}

#[inline]
pub unsafe fn mk_seq_sort(c: Context, s: Sort) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_sort(c, s) }, "Z3_mk_seq_sort")
}

/// Returns the built-in string sort (sequence of characters).
/// Replaces `mk_seq_sort(ctx, mk_char_sort(ctx))`.
#[inline]
pub unsafe fn mk_string_sort(c: Context) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_mk_string_sort(c) }, "Z3_mk_string_sort")
}

// ── Sort inspection ──────────────────────────────────────────────────

#[inline]
pub unsafe fn get_sort(c: Context, a: Ast) -> Sort {
    unwrap_z3(unsafe { z3_sys::Z3_get_sort(c, a) }, "Z3_get_sort")
}

pub use z3_sys::Z3_fpa_get_ebits as fpa_get_ebits;
pub use z3_sys::Z3_fpa_get_sbits as fpa_get_sbits;
pub use z3_sys::Z3_get_bv_sort_size as get_bv_sort_size;
pub use z3_sys::Z3_get_sort_kind as get_sort_kind;

// ── AST construction – constants & numerals ──────────────────────────

#[inline]
pub unsafe fn mk_true(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_true(c) }, "Z3_mk_true")
}

#[inline]
pub unsafe fn mk_false(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_false(c) }, "Z3_mk_false")
}

#[inline]
pub unsafe fn mk_const(c: Context, s: Symbol, ty: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_const(c, s, ty) }, "Z3_mk_const")
}

#[inline]
pub unsafe fn mk_numeral(c: Context, numeral: z3_sys::Z3_string, ty: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_numeral(c, numeral, ty) }, "Z3_mk_numeral")
}

#[inline]
pub unsafe fn mk_int(c: Context, v: ::std::os::raw::c_int, ty: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_int(c, v, ty) }, "Z3_mk_int")
}

#[inline]
pub unsafe fn mk_func_decl(
    c: Context,
    s: Symbol,
    domain_size: c_uint,
    domain: *const Sort,
    range: Sort,
) -> FuncDecl {
    unwrap_z3(
        unsafe { z3_sys::Z3_mk_func_decl(c, s, domain_size, domain, range) },
        "Z3_mk_func_decl",
    )
}

#[inline]
pub unsafe fn mk_app(
    c: Context,
    d: FuncDecl,
    num_args: c_uint,
    args: *const Ast,
) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_app(c, d, num_args, args) }, "Z3_mk_app")
}

#[inline]
pub unsafe fn mk_string(c: Context, s: z3_sys::Z3_string) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_string(c, s) }, "Z3_mk_string")
}

// ── AST construction – Boolean ───────────────────────────────────────

#[inline]
pub unsafe fn mk_not(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_not(c, a) }, "Z3_mk_not")
}

#[inline]
pub unsafe fn mk_and(c: Context, num_args: c_uint, args: *const Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_and(c, num_args, args) }, "Z3_mk_and")
}

#[inline]
pub unsafe fn mk_or(c: Context, num_args: c_uint, args: *const Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_or(c, num_args, args) }, "Z3_mk_or")
}

#[inline]
pub unsafe fn mk_xor(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_xor(c, a, b) }, "Z3_mk_xor")
}

#[inline]
pub unsafe fn mk_eq(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_eq(c, a, b) }, "Z3_mk_eq")
}

#[inline]
pub unsafe fn mk_distinct(c: Context, num_args: c_uint, args: *const Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_distinct(c, num_args, args) }, "Z3_mk_distinct")
}

#[inline]
pub unsafe fn mk_ite(c: Context, t1: Ast, t2: Ast, t3: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_ite(c, t1, t2, t3) }, "Z3_mk_ite")
}

#[inline]
pub unsafe fn mk_ge(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_ge(c, a, b) }, "Z3_mk_ge")
}

#[inline]
pub unsafe fn mk_gt(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_gt(c, a, b) }, "Z3_mk_gt")
}

// ── AST construction – Bit-vector ────────────────────────────────────

#[inline]
pub unsafe fn mk_bvnot(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvnot(c, a) }, "Z3_mk_bvnot")
}

#[inline]
pub unsafe fn mk_bvneg(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvneg(c, a) }, "Z3_mk_bvneg")
}

#[inline]
pub unsafe fn mk_bvand(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvand(c, a, b) }, "Z3_mk_bvand")
}

#[inline]
pub unsafe fn mk_bvor(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvor(c, a, b) }, "Z3_mk_bvor")
}

#[inline]
pub unsafe fn mk_bvxor(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvxor(c, a, b) }, "Z3_mk_bvxor")
}

#[inline]
pub unsafe fn mk_bvadd(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvadd(c, a, b) }, "Z3_mk_bvadd")
}

#[inline]
pub unsafe fn mk_bvsub(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvsub(c, a, b) }, "Z3_mk_bvsub")
}

#[inline]
pub unsafe fn mk_bvmul(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvmul(c, a, b) }, "Z3_mk_bvmul")
}

#[inline]
pub unsafe fn mk_bvudiv(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvudiv(c, a, b) }, "Z3_mk_bvudiv")
}

#[inline]
pub unsafe fn mk_bvsdiv(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvsdiv(c, a, b) }, "Z3_mk_bvsdiv")
}

#[inline]
pub unsafe fn mk_bvurem(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvurem(c, a, b) }, "Z3_mk_bvurem")
}

#[inline]
pub unsafe fn mk_bvsrem(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvsrem(c, a, b) }, "Z3_mk_bvsrem")
}

#[inline]
pub unsafe fn mk_bvshl(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvshl(c, a, b) }, "Z3_mk_bvshl")
}

#[inline]
pub unsafe fn mk_bvlshr(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvlshr(c, a, b) }, "Z3_mk_bvlshr")
}

#[inline]
pub unsafe fn mk_bvashr(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvashr(c, a, b) }, "Z3_mk_bvashr")
}

#[inline]
pub unsafe fn mk_ext_rotate_left(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_ext_rotate_left(c, a, b) }, "Z3_mk_ext_rotate_left")
}

#[inline]
pub unsafe fn mk_ext_rotate_right(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_ext_rotate_right(c, a, b) }, "Z3_mk_ext_rotate_right")
}

#[inline]
pub unsafe fn mk_zero_ext(c: Context, i: c_uint, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_zero_ext(c, i, a) }, "Z3_mk_zero_ext")
}

#[inline]
pub unsafe fn mk_sign_ext(c: Context, i: c_uint, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_sign_ext(c, i, a) }, "Z3_mk_sign_ext")
}

#[inline]
pub unsafe fn mk_extract(c: Context, high: c_uint, low: c_uint, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_extract(c, high, low, a) }, "Z3_mk_extract")
}

#[inline]
pub unsafe fn mk_concat(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_concat(c, a, b) }, "Z3_mk_concat")
}

#[inline]
pub unsafe fn mk_int2bv(c: Context, n: c_uint, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_int2bv(c, n, a) }, "Z3_mk_int2bv")
}

#[inline]
pub unsafe fn mk_bv2int(c: Context, a: Ast, is_signed: bool) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bv2int(c, a, is_signed) }, "Z3_mk_bv2int")
}

// ── BV comparisons ──────────────────────────────────────────────────

#[inline]
pub unsafe fn mk_bvult(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvult(c, a, b) }, "Z3_mk_bvult")
}

#[inline]
pub unsafe fn mk_bvule(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvule(c, a, b) }, "Z3_mk_bvule")
}

#[inline]
pub unsafe fn mk_bvugt(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvugt(c, a, b) }, "Z3_mk_bvugt")
}

#[inline]
pub unsafe fn mk_bvuge(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvuge(c, a, b) }, "Z3_mk_bvuge")
}

#[inline]
pub unsafe fn mk_bvslt(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvslt(c, a, b) }, "Z3_mk_bvslt")
}

#[inline]
pub unsafe fn mk_bvsle(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvsle(c, a, b) }, "Z3_mk_bvsle")
}

#[inline]
pub unsafe fn mk_bvsgt(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvsgt(c, a, b) }, "Z3_mk_bvsgt")
}

#[inline]
pub unsafe fn mk_bvsge(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_bvsge(c, a, b) }, "Z3_mk_bvsge")
}

// ── AST construction – Floating-point ────────────────────────────────

#[inline]
pub unsafe fn mk_fpa_rne(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_rne(c) }, "Z3_mk_fpa_rne")
}

#[inline]
pub unsafe fn mk_fpa_rtp(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_rtp(c) }, "Z3_mk_fpa_rtp")
}

#[inline]
pub unsafe fn mk_fpa_rtn(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_rtn(c) }, "Z3_mk_fpa_rtn")
}

#[inline]
pub unsafe fn mk_fpa_rtz(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_rtz(c) }, "Z3_mk_fpa_rtz")
}

#[inline]
pub unsafe fn mk_fpa_rna(c: Context) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_rna(c) }, "Z3_mk_fpa_rna")
}

#[inline]
pub unsafe fn mk_fpa_numeral_float(c: Context, v: f32, ty: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_numeral_float(c, v, ty) }, "Z3_mk_fpa_numeral_float")
}

#[inline]
pub unsafe fn mk_fpa_numeral_double(c: Context, v: f64, ty: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_numeral_double(c, v, ty) }, "Z3_mk_fpa_numeral_double")
}

#[inline]
pub unsafe fn mk_fpa_neg(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_neg(c, a) }, "Z3_mk_fpa_neg")
}

#[inline]
pub unsafe fn mk_fpa_abs(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_abs(c, a) }, "Z3_mk_fpa_abs")
}

#[inline]
pub unsafe fn mk_fpa_add(c: Context, rm: Ast, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_add(c, rm, a, b) }, "Z3_mk_fpa_add")
}

#[inline]
pub unsafe fn mk_fpa_sub(c: Context, rm: Ast, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_sub(c, rm, a, b) }, "Z3_mk_fpa_sub")
}

#[inline]
pub unsafe fn mk_fpa_mul(c: Context, rm: Ast, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_mul(c, rm, a, b) }, "Z3_mk_fpa_mul")
}

#[inline]
pub unsafe fn mk_fpa_div(c: Context, rm: Ast, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_div(c, rm, a, b) }, "Z3_mk_fpa_div")
}

#[inline]
pub unsafe fn mk_fpa_sqrt(c: Context, rm: Ast, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_sqrt(c, rm, a) }, "Z3_mk_fpa_sqrt")
}

#[inline]
pub unsafe fn mk_fpa_eq(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_eq(c, a, b) }, "Z3_mk_fpa_eq")
}

#[inline]
pub unsafe fn mk_fpa_lt(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_lt(c, a, b) }, "Z3_mk_fpa_lt")
}

#[inline]
pub unsafe fn mk_fpa_leq(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_leq(c, a, b) }, "Z3_mk_fpa_leq")
}

#[inline]
pub unsafe fn mk_fpa_gt(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_gt(c, a, b) }, "Z3_mk_fpa_gt")
}

#[inline]
pub unsafe fn mk_fpa_geq(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_geq(c, a, b) }, "Z3_mk_fpa_geq")
}

#[inline]
pub unsafe fn mk_fpa_is_nan(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_is_nan(c, a) }, "Z3_mk_fpa_is_nan")
}

#[inline]
pub unsafe fn mk_fpa_is_infinite(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_is_infinite(c, a) }, "Z3_mk_fpa_is_infinite")
}

#[inline]
pub unsafe fn mk_fpa_fp(c: Context, sgn: Ast, exp: Ast, sig: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_fp(c, sgn, exp, sig) }, "Z3_mk_fpa_fp")
}

#[inline]
pub unsafe fn mk_fpa_to_fp_bv(c: Context, bv: Ast, s: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_fp_bv(c, bv, s) }, "Z3_mk_fpa_to_fp_bv")
}

#[inline]
pub unsafe fn mk_fpa_to_fp_float(c: Context, rm: Ast, a: Ast, s: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_fp_float(c, rm, a, s) }, "Z3_mk_fpa_to_fp_float")
}

#[inline]
pub unsafe fn mk_fpa_to_fp_signed(c: Context, rm: Ast, a: Ast, s: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_fp_signed(c, rm, a, s) }, "Z3_mk_fpa_to_fp_signed")
}

#[inline]
pub unsafe fn mk_fpa_to_fp_unsigned(c: Context, rm: Ast, a: Ast, s: Sort) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_fp_unsigned(c, rm, a, s) }, "Z3_mk_fpa_to_fp_unsigned")
}

#[inline]
pub unsafe fn mk_fpa_to_ieee_bv(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_ieee_bv(c, a) }, "Z3_mk_fpa_to_ieee_bv")
}

#[inline]
pub unsafe fn mk_fpa_to_ubv(c: Context, rm: Ast, a: Ast, sz: c_uint) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_ubv(c, rm, a, sz) }, "Z3_mk_fpa_to_ubv")
}

#[inline]
pub unsafe fn mk_fpa_to_sbv(c: Context, rm: Ast, a: Ast, sz: c_uint) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_fpa_to_sbv(c, rm, a, sz) }, "Z3_mk_fpa_to_sbv")
}

// ── AST construction – Sequences / Strings ───────────────────────────

#[inline]
pub unsafe fn mk_seq_concat(c: Context, n: c_uint, args: *const Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_concat(c, n, args) }, "Z3_mk_seq_concat")
}

#[inline]
pub unsafe fn mk_seq_prefix(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_prefix(c, a, b) }, "Z3_mk_seq_prefix")
}

#[inline]
pub unsafe fn mk_seq_suffix(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_suffix(c, a, b) }, "Z3_mk_seq_suffix")
}

#[inline]
pub unsafe fn mk_seq_contains(c: Context, a: Ast, b: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_contains(c, a, b) }, "Z3_mk_seq_contains")
}

#[inline]
pub unsafe fn mk_seq_extract(c: Context, s: Ast, offset: Ast, length: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_extract(c, s, offset, length) }, "Z3_mk_seq_extract")
}

#[inline]
pub unsafe fn mk_seq_replace(c: Context, s: Ast, src: Ast, dst: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_replace(c, s, src, dst) }, "Z3_mk_seq_replace")
}

#[inline]
pub unsafe fn mk_seq_index(c: Context, s: Ast, substr: Ast, offset: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_index(c, s, substr, offset) }, "Z3_mk_seq_index")
}

#[inline]
pub unsafe fn mk_seq_length(c: Context, s: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_seq_length(c, s) }, "Z3_mk_seq_length")
}

#[inline]
pub unsafe fn mk_str_to_int(c: Context, s: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_str_to_int(c, s) }, "Z3_mk_str_to_int")
}

#[inline]
pub unsafe fn mk_int_to_str(c: Context, s: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_mk_int_to_str(c, s) }, "Z3_mk_int_to_str")
}

// ── AST inspection ───────────────────────────────────────────────────

#[inline]
pub unsafe fn to_app(c: Context, a: Ast) -> App {
    unwrap_z3(unsafe { z3_sys::Z3_to_app(c, a) }, "Z3_to_app")
}

#[inline]
pub unsafe fn get_app_decl(c: Context, a: App) -> FuncDecl {
    unwrap_z3(unsafe { z3_sys::Z3_get_app_decl(c, a) }, "Z3_get_app_decl")
}

#[inline]
pub unsafe fn get_app_arg(c: Context, a: App, i: c_uint) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_get_app_arg(c, a, i) }, "Z3_get_app_arg")
}

#[inline]
pub unsafe fn get_decl_name(c: Context, d: FuncDecl) -> Symbol {
    unwrap_z3(unsafe { z3_sys::Z3_get_decl_name(c, d) }, "Z3_get_decl_name")
}

#[inline]
pub unsafe fn simplify(c: Context, a: Ast) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_simplify(c, a) }, "Z3_simplify")
}

pub use z3_sys::Z3_func_decl_to_string as func_decl_to_string;
pub use z3_sys::Z3_get_app_num_args as get_app_num_args;
pub use z3_sys::Z3_get_ast_kind as get_ast_kind;
pub use z3_sys::Z3_get_decl_int_parameter as get_decl_int_parameter;
pub use z3_sys::Z3_get_decl_kind as get_decl_kind;
pub use z3_sys::Z3_get_numeral_double as get_numeral_double;
pub use z3_sys::Z3_get_numeral_int as get_numeral_int;
pub use z3_sys::Z3_get_numeral_string as get_numeral_string;
pub use z3_sys::Z3_get_string as get_string;
pub use z3_sys::Z3_get_symbol_string as get_symbol_string;
pub use z3_sys::Z3_is_string as is_string;

// ── Reference counting ──────────────────────────────────────────────
pub use z3_sys::Z3_dec_ref as dec_ref;
pub use z3_sys::Z3_inc_ref as inc_ref;

// ── Params ───────────────────────────────────────────────────────────

#[inline]
pub unsafe fn mk_params(c: Context) -> Params {
    unwrap_z3(unsafe { z3_sys::Z3_mk_params(c) }, "Z3_mk_params")
}

pub use z3_sys::Z3_params_dec_ref as params_dec_ref;
pub use z3_sys::Z3_params_inc_ref as params_inc_ref;
pub use z3_sys::Z3_params_set_bool as params_set_bool;
pub use z3_sys::Z3_params_set_uint as params_set_uint;

// ── Solver ───────────────────────────────────────────────────────────

#[inline]
pub unsafe fn mk_solver(c: Context) -> Solver {
    unwrap_z3(unsafe { z3_sys::Z3_mk_solver(c) }, "Z3_mk_solver")
}

pub use z3_sys::Z3_solver_assert as solver_assert;
pub use z3_sys::Z3_solver_assert_and_track as solver_assert_and_track;
pub use z3_sys::Z3_solver_dec_ref as solver_dec_ref;
pub use z3_sys::Z3_solver_inc_ref as solver_inc_ref;
pub use z3_sys::Z3_solver_set_params as solver_set_params;

#[inline]
pub unsafe fn solver_check(ctx: Context, solver: Solver) -> Lbool {
    unsafe { z3_sys::Z3_solver_check(ctx, solver) }.into()
}

#[inline]
pub unsafe fn solver_check_assumptions(
    ctx: Context,
    solver: Solver,
    num_assumptions: c_uint,
    assumptions: *const Ast,
) -> Lbool {
    unsafe { z3_sys::Z3_solver_check_assumptions(ctx, solver, num_assumptions, assumptions) }.into()
}

#[inline]
pub unsafe fn solver_get_model(c: Context, s: Solver) -> Model {
    unwrap_z3(unsafe { z3_sys::Z3_solver_get_model(c, s) }, "Z3_solver_get_model")
}

#[inline]
pub unsafe fn solver_get_unsat_core(c: Context, s: Solver) -> AstVector {
    unwrap_z3(unsafe { z3_sys::Z3_solver_get_unsat_core(c, s) }, "Z3_solver_get_unsat_core")
}

// ── Optimize ─────────────────────────────────────────────────────────

#[inline]
pub unsafe fn mk_optimize(c: Context) -> Optimize {
    unwrap_z3(unsafe { z3_sys::Z3_mk_optimize(c) }, "Z3_mk_optimize")
}

pub use z3_sys::Z3_optimize_assert as optimize_assert;
pub use z3_sys::Z3_optimize_dec_ref as optimize_dec_ref;
pub use z3_sys::Z3_optimize_inc_ref as optimize_inc_ref;

#[inline]
pub unsafe fn optimize_assert_soft(
    c: Context,
    o: Optimize,
    a: Ast,
    weight: z3_sys::Z3_string,
    id: Option<z3_sys::Z3_symbol>,
) -> c_uint {
    unsafe { z3_sys::Z3_optimize_assert_soft(c, o, a, weight, id) }
}

#[inline]
pub unsafe fn optimize_minimize(c: Context, o: Optimize, a: Ast) {
    unsafe { z3_sys::Z3_optimize_minimize(c, o, a); }
}

#[inline]
pub unsafe fn optimize_maximize(c: Context, o: Optimize, a: Ast) {
    unsafe { z3_sys::Z3_optimize_maximize(c, o, a); }
}

#[inline]
pub unsafe fn optimize_check(
    ctx: Context,
    opt: Optimize,
    num_assumptions: c_uint,
    assumptions: *const Ast,
) -> Lbool {
    unsafe { z3_sys::Z3_optimize_check(ctx, opt, num_assumptions, assumptions) }.into()
}

#[inline]
pub unsafe fn optimize_get_model(c: Context, o: Optimize) -> Model {
    unwrap_z3(unsafe { z3_sys::Z3_optimize_get_model(c, o) }, "Z3_optimize_get_model")
}

// ── Model ────────────────────────────────────────────────────────────
pub use z3_sys::Z3_model_dec_ref as model_dec_ref;
pub use z3_sys::Z3_model_eval as model_eval;
pub use z3_sys::Z3_model_inc_ref as model_inc_ref;

// ── AST Vector ───────────────────────────────────────────────────────

#[inline]
pub unsafe fn ast_vector_get(c: Context, v: AstVector, i: c_uint) -> Ast {
    unwrap_z3(unsafe { z3_sys::Z3_ast_vector_get(c, v, i) }, "Z3_ast_vector_get")
}

pub use z3_sys::Z3_ast_vector_dec_ref as ast_vector_dec_ref;
pub use z3_sys::Z3_ast_vector_inc_ref as ast_vector_inc_ref;
pub use z3_sys::Z3_ast_vector_size as ast_vector_size;
