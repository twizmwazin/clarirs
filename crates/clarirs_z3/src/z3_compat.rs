//! Compatibility layer mapping `z3-sys` (prove-rs) names to the naming
//! convention used throughout clarirs.
//!
//! The previous `clarirs-z3-sys` crate stripped the `Z3_` prefix from all
//! names and converted types/enum-variants to PascalCase.  Rather than
//! rewriting every call-site, this module re-exports the `z3_sys` items
//! under the old names so that `use crate::z3_compat as z3;` is a drop-in
//! replacement for the old `use clarirs_z3_sys as z3;`.
//!
//! Because the prove-rs `z3-sys` returns `Option<NonNull<…>>` from most
//! creating functions, we unwrap these `Option`s here.  Z3 only returns
//! null on catastrophic allocation failure, which is unrecoverable anyway.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::missing_safety_doc)]
#![allow(unused_imports)]
#![allow(dead_code)]

use std::ffi::c_char;

// ── Type aliases ────────────────────────────────────────────────────────

pub type Context = z3_sys::Z3_context;
pub type Ast = z3_sys::Z3_ast;
pub type Sort = z3_sys::Z3_sort;
pub type Config = z3_sys::Z3_config;
pub type Solver = z3_sys::Z3_solver;
pub type Model = z3_sys::Z3_model;
pub type Params = z3_sys::Z3_params;
pub type Optimize = z3_sys::Z3_optimize;
pub type AstVector = z3_sys::Z3_ast_vector;
pub type App = z3_sys::Z3_app;
pub type Symbol = z3_sys::Z3_symbol;
pub type FuncDecl = z3_sys::Z3_func_decl;

// ── Enum re-exports ─────────────────────────────────────────────────────

pub use z3_sys::Z3_ast_kind as AstKind;
pub use z3_sys::Z3_decl_kind as DeclKind;
pub use z3_sys::Z3_error_code as ErrorCode;
pub use z3_sys::Z3_sort_kind as SortKind;

// ── Lbool ───────────────────────────────────────────────────────────────

#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lbool {
    False = -1,
    Undef = 0,
    True = 1,
}

impl From<z3_sys::Z3_lbool> for Lbool {
    fn from(val: z3_sys::Z3_lbool) -> Self {
        match val {
            z3_sys::Z3_L_FALSE => Lbool::False,
            z3_sys::Z3_L_TRUE => Lbool::True,
            _ => Lbool::Undef,
        }
    }
}

// ── Helper to unwrap Option<NonNull> returns ────────────────────────────
//
// Nearly every Z3 "constructor" function returns `Option<NonNull<…>>` in
// the prove-rs bindings.  A `None` result means the C function returned
// NULL, which in practice only happens on catastrophic allocation failure
// inside Z3. We unwrap here so that call-sites remain unchanged.

trait Z3Expect {
    type Inner;
    fn z3(self) -> Self::Inner;
}

impl<T> Z3Expect for Option<T> {
    type Inner = T;
    #[inline]
    fn z3(self) -> T {
        self.expect("z3 returned null")
    }
}

// ── Context / Config ────────────────────────────────────────────────────

pub unsafe fn mk_config() -> Config {
    unsafe { z3_sys::Z3_mk_config().z3() }
}

pub unsafe fn mk_context(c: Config) -> Context {
    unsafe { z3_sys::Z3_mk_context(c).z3() }
}

pub use z3_sys::Z3_del_config as del_config;
pub use z3_sys::Z3_del_context as del_context;
pub use z3_sys::Z3_set_error_handler as set_error_handler;
pub use z3_sys::Z3_get_error_code as get_error_code;
pub use z3_sys::Z3_get_error_msg as get_error_msg;

// ── Sorts ───────────────────────────────────────────────────────────────

pub unsafe fn mk_bool_sort(c: Context) -> Sort {
    unsafe { z3_sys::Z3_mk_bool_sort(c).z3() }
}
pub unsafe fn mk_int_sort(c: Context) -> Sort {
    unsafe { z3_sys::Z3_mk_int_sort(c).z3() }
}
pub unsafe fn mk_bv_sort(c: Context, sz: u32) -> Sort {
    unsafe { z3_sys::Z3_mk_bv_sort(c, sz).z3() }
}
pub unsafe fn mk_fpa_sort(c: Context, ebits: u32, sbits: u32) -> Sort {
    unsafe { z3_sys::Z3_mk_fpa_sort(c, ebits, sbits).z3() }
}
pub unsafe fn mk_seq_sort(c: Context, s: Sort) -> Sort {
    unsafe { z3_sys::Z3_mk_seq_sort(c, s).z3() }
}
pub unsafe fn mk_char_sort(c: Context) -> Sort {
    unsafe { z3_sys::Z3_mk_char_sort(c).z3() }
}

// ── Symbols / Constants / Applications ──────────────────────────────────

pub unsafe fn mk_string_symbol(c: Context, s: *const c_char) -> Symbol {
    unsafe { z3_sys::Z3_mk_string_symbol(c, s).z3() }
}
pub unsafe fn mk_const(c: Context, s: Symbol, ty: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_const(c, s, ty).z3() }
}
pub unsafe fn mk_func_decl(
    c: Context,
    s: Symbol,
    domain_size: u32,
    domain: *const Sort,
    range: Sort,
) -> FuncDecl {
    unsafe { z3_sys::Z3_mk_func_decl(c, s, domain_size, domain, range).z3() }
}
pub unsafe fn mk_app(
    c: Context,
    d: FuncDecl,
    num_args: u32,
    args: *const Ast,
) -> Ast {
    unsafe { z3_sys::Z3_mk_app(c, d, num_args, args).z3() }
}
pub unsafe fn mk_numeral(c: Context, numeral: *const c_char, ty: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_numeral(c, numeral, ty).z3() }
}

// ── Boolean operations ──────────────────────────────────────────────────

pub unsafe fn mk_true(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_true(c).z3() }
}
pub unsafe fn mk_false(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_false(c).z3() }
}
pub unsafe fn mk_not(c: Context, a: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_not(c, a).z3() }
}
pub unsafe fn mk_and(c: Context, num_args: u32, args: *const Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_and(c, num_args, args).z3() }
}
pub unsafe fn mk_or(c: Context, num_args: u32, args: *const Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_or(c, num_args, args).z3() }
}
pub unsafe fn mk_xor(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_xor(c, t1, t2).z3() }
}
pub unsafe fn mk_eq(c: Context, l: Ast, r: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_eq(c, l, r).z3() }
}
pub unsafe fn mk_distinct(c: Context, num_args: u32, args: *const Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_distinct(c, num_args, args).z3() }
}
pub unsafe fn mk_ite(c: Context, t1: Ast, t2: Ast, t3: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_ite(c, t1, t2, t3).z3() }
}

// ── Arithmetic (used for string digit check) ────────────────────────────

pub unsafe fn mk_ge(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_ge(c, t1, t2).z3() }
}
pub unsafe fn mk_gt(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_gt(c, t1, t2).z3() }
}

// ── Bitvector operations ────────────────────────────────────────────────

pub unsafe fn mk_bvnot(c: Context, t1: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvnot(c, t1).z3() }
}
pub unsafe fn mk_bvneg(c: Context, t1: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvneg(c, t1).z3() }
}
pub unsafe fn mk_bvand(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvand(c, t1, t2).z3() }
}
pub unsafe fn mk_bvor(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvor(c, t1, t2).z3() }
}
pub unsafe fn mk_bvxor(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvxor(c, t1, t2).z3() }
}
pub unsafe fn mk_bvadd(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvadd(c, t1, t2).z3() }
}
pub unsafe fn mk_bvsub(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvsub(c, t1, t2).z3() }
}
pub unsafe fn mk_bvmul(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvmul(c, t1, t2).z3() }
}
pub unsafe fn mk_bvudiv(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvudiv(c, t1, t2).z3() }
}
pub unsafe fn mk_bvsdiv(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvsdiv(c, t1, t2).z3() }
}
pub unsafe fn mk_bvurem(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvurem(c, t1, t2).z3() }
}
pub unsafe fn mk_bvsrem(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvsrem(c, t1, t2).z3() }
}
pub unsafe fn mk_bvshl(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvshl(c, t1, t2).z3() }
}
pub unsafe fn mk_bvlshr(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvlshr(c, t1, t2).z3() }
}
pub unsafe fn mk_bvashr(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvashr(c, t1, t2).z3() }
}
pub unsafe fn mk_ext_rotate_left(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_ext_rotate_left(c, t1, t2).z3() }
}
pub unsafe fn mk_ext_rotate_right(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_ext_rotate_right(c, t1, t2).z3() }
}
pub unsafe fn mk_zero_ext(c: Context, i: u32, t1: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_zero_ext(c, i, t1).z3() }
}
pub unsafe fn mk_sign_ext(c: Context, i: u32, t1: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_sign_ext(c, i, t1).z3() }
}
pub unsafe fn mk_extract(c: Context, high: u32, low: u32, t1: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_extract(c, high, low, t1).z3() }
}
pub unsafe fn mk_concat(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_concat(c, t1, t2).z3() }
}
pub unsafe fn mk_bvult(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvult(c, t1, t2).z3() }
}
pub unsafe fn mk_bvule(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvule(c, t1, t2).z3() }
}
pub unsafe fn mk_bvugt(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvugt(c, t1, t2).z3() }
}
pub unsafe fn mk_bvuge(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvuge(c, t1, t2).z3() }
}
pub unsafe fn mk_bvslt(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvslt(c, t1, t2).z3() }
}
pub unsafe fn mk_bvsle(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvsle(c, t1, t2).z3() }
}
pub unsafe fn mk_bvsgt(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvsgt(c, t1, t2).z3() }
}
pub unsafe fn mk_bvsge(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_bvsge(c, t1, t2).z3() }
}
pub unsafe fn mk_bv2int(c: Context, t1: Ast, is_signed: bool) -> Ast {
    unsafe { z3_sys::Z3_mk_bv2int(c, t1, is_signed).z3() }
}
pub unsafe fn mk_int2bv(c: Context, n: u32, t1: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_int2bv(c, n, t1).z3() }
}

// ── Floating-point operations ───────────────────────────────────────────

pub unsafe fn mk_fpa_rne(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_rne(c).z3() }
}
pub unsafe fn mk_fpa_rtp(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_rtp(c).z3() }
}
pub unsafe fn mk_fpa_rtn(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_rtn(c).z3() }
}
pub unsafe fn mk_fpa_rtz(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_rtz(c).z3() }
}
pub unsafe fn mk_fpa_rna(c: Context) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_rna(c).z3() }
}
pub unsafe fn mk_fpa_numeral_float(c: Context, v: f32, ty: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_numeral_float(c, v, ty).z3() }
}
pub unsafe fn mk_fpa_numeral_double(c: Context, v: f64, ty: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_numeral_double(c, v, ty).z3() }
}
pub unsafe fn mk_fpa_neg(c: Context, t: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_neg(c, t).z3() }
}
pub unsafe fn mk_fpa_abs(c: Context, t: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_abs(c, t).z3() }
}
pub unsafe fn mk_fpa_add(c: Context, rm: Ast, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_add(c, rm, t1, t2).z3() }
}
pub unsafe fn mk_fpa_sub(c: Context, rm: Ast, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_sub(c, rm, t1, t2).z3() }
}
pub unsafe fn mk_fpa_mul(c: Context, rm: Ast, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_mul(c, rm, t1, t2).z3() }
}
pub unsafe fn mk_fpa_div(c: Context, rm: Ast, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_div(c, rm, t1, t2).z3() }
}
pub unsafe fn mk_fpa_sqrt(c: Context, rm: Ast, t: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_sqrt(c, rm, t).z3() }
}
pub unsafe fn mk_fpa_eq(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_eq(c, t1, t2).z3() }
}
pub unsafe fn mk_fpa_lt(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_lt(c, t1, t2).z3() }
}
pub unsafe fn mk_fpa_leq(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_leq(c, t1, t2).z3() }
}
pub unsafe fn mk_fpa_gt(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_gt(c, t1, t2).z3() }
}
pub unsafe fn mk_fpa_geq(c: Context, t1: Ast, t2: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_geq(c, t1, t2).z3() }
}
pub unsafe fn mk_fpa_is_nan(c: Context, t: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_is_nan(c, t).z3() }
}
pub unsafe fn mk_fpa_is_infinite(c: Context, t: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_is_infinite(c, t).z3() }
}
pub unsafe fn mk_fpa_to_fp_float(c: Context, rm: Ast, t: Ast, s: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_fp_float(c, rm, t, s).z3() }
}
pub unsafe fn mk_fpa_to_fp_bv(c: Context, bv: Ast, s: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_fp_bv(c, bv, s).z3() }
}
pub unsafe fn mk_fpa_to_fp_signed(c: Context, rm: Ast, t: Ast, s: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_fp_signed(c, rm, t, s).z3() }
}
pub unsafe fn mk_fpa_to_fp_unsigned(c: Context, rm: Ast, t: Ast, s: Sort) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_fp_unsigned(c, rm, t, s).z3() }
}
pub unsafe fn mk_fpa_fp(c: Context, sgn: Ast, exp: Ast, sig: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_fp(c, sgn, exp, sig).z3() }
}
pub unsafe fn mk_fpa_to_ieee_bv(c: Context, t: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_ieee_bv(c, t).z3() }
}
pub unsafe fn mk_fpa_to_ubv(c: Context, rm: Ast, t: Ast, sz: u32) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_ubv(c, rm, t, sz).z3() }
}
pub unsafe fn mk_fpa_to_sbv(c: Context, rm: Ast, t: Ast, sz: u32) -> Ast {
    unsafe { z3_sys::Z3_mk_fpa_to_sbv(c, rm, t, sz).z3() }
}

// ── String / Sequence operations ────────────────────────────────────────

pub unsafe fn mk_string(c: Context, s: *const c_char) -> Ast {
    unsafe { z3_sys::Z3_mk_string(c, s).z3() }
}
pub unsafe fn mk_seq_concat(c: Context, n: u32, args: *const Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_concat(c, n, args).z3() }
}
pub unsafe fn mk_seq_extract(c: Context, s: Ast, offset: Ast, length: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_extract(c, s, offset, length).z3() }
}
pub unsafe fn mk_seq_replace(c: Context, s: Ast, src: Ast, dst: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_replace(c, s, src, dst).z3() }
}
pub unsafe fn mk_seq_contains(c: Context, s: Ast, sub: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_contains(c, s, sub).z3() }
}
pub unsafe fn mk_seq_prefix(c: Context, pre: Ast, s: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_prefix(c, pre, s).z3() }
}
pub unsafe fn mk_seq_suffix(c: Context, suf: Ast, s: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_suffix(c, suf, s).z3() }
}
pub unsafe fn mk_seq_index(c: Context, s: Ast, substr: Ast, offset: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_index(c, s, substr, offset).z3() }
}
pub unsafe fn mk_seq_length(c: Context, s: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_seq_length(c, s).z3() }
}
pub unsafe fn mk_str_to_int(c: Context, s: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_str_to_int(c, s).z3() }
}
pub unsafe fn mk_int_to_str(c: Context, s: Ast) -> Ast {
    unsafe { z3_sys::Z3_mk_int_to_str(c, s).z3() }
}

// ── Params ──────────────────────────────────────────────────────────────

pub unsafe fn mk_params(c: Context) -> Params {
    unsafe { z3_sys::Z3_mk_params(c).z3() }
}
pub use z3_sys::Z3_params_inc_ref as params_inc_ref;
pub use z3_sys::Z3_params_dec_ref as params_dec_ref;
pub use z3_sys::Z3_params_set_bool as params_set_bool;
pub use z3_sys::Z3_params_set_uint as params_set_uint;

// ── Solver ──────────────────────────────────────────────────────────────

pub unsafe fn mk_solver(c: Context) -> Solver {
    unsafe { z3_sys::Z3_mk_solver(c).z3() }
}
pub use z3_sys::Z3_solver_inc_ref as solver_inc_ref;
pub use z3_sys::Z3_solver_dec_ref as solver_dec_ref;
pub use z3_sys::Z3_solver_assert as solver_assert;
pub use z3_sys::Z3_solver_assert_and_track as solver_assert_and_track;
pub use z3_sys::Z3_solver_set_params as solver_set_params;

pub unsafe fn solver_check(ctx: Context, solver: Solver) -> Lbool {
    unsafe { z3_sys::Z3_solver_check(ctx, solver).into() }
}

pub unsafe fn solver_check_assumptions(
    ctx: Context,
    solver: Solver,
    num_assumptions: u32,
    assumptions: *const Ast,
) -> Lbool {
    unsafe {
        z3_sys::Z3_solver_check_assumptions(ctx, solver, num_assumptions, assumptions).into()
    }
}

pub unsafe fn solver_get_model(c: Context, s: Solver) -> Model {
    unsafe { z3_sys::Z3_solver_get_model(c, s).z3() }
}
pub unsafe fn solver_get_unsat_core(c: Context, s: Solver) -> AstVector {
    unsafe { z3_sys::Z3_solver_get_unsat_core(c, s).z3() }
}

// ── Optimize ────────────────────────────────────────────────────────────

pub unsafe fn mk_optimize(c: Context) -> Optimize {
    unsafe { z3_sys::Z3_mk_optimize(c).z3() }
}
pub use z3_sys::Z3_optimize_inc_ref as optimize_inc_ref;
pub use z3_sys::Z3_optimize_dec_ref as optimize_dec_ref;
pub use z3_sys::Z3_optimize_assert as optimize_assert;
pub use z3_sys::Z3_optimize_assert_soft as optimize_assert_soft;
pub use z3_sys::Z3_optimize_minimize as optimize_minimize;
pub use z3_sys::Z3_optimize_maximize as optimize_maximize;

pub unsafe fn optimize_check(
    ctx: Context,
    optimize: Optimize,
    num_assumptions: u32,
    assumptions: *const Ast,
) -> Lbool {
    unsafe { z3_sys::Z3_optimize_check(ctx, optimize, num_assumptions, assumptions).into() }
}

pub unsafe fn optimize_get_model(c: Context, o: Optimize) -> Model {
    unsafe { z3_sys::Z3_optimize_get_model(c, o).z3() }
}

// ── Model ───────────────────────────────────────────────────────────────

pub use z3_sys::Z3_model_inc_ref as model_inc_ref;
pub use z3_sys::Z3_model_dec_ref as model_dec_ref;
pub use z3_sys::Z3_model_eval as model_eval;

// ── AST vector ──────────────────────────────────────────────────────────

pub use z3_sys::Z3_ast_vector_inc_ref as ast_vector_inc_ref;
pub use z3_sys::Z3_ast_vector_dec_ref as ast_vector_dec_ref;
pub use z3_sys::Z3_ast_vector_size as ast_vector_size;

pub unsafe fn ast_vector_get(c: Context, v: AstVector, i: u32) -> Ast {
    unsafe { z3_sys::Z3_ast_vector_get(c, v, i).z3() }
}

// ── Reference counting ─────────────────────────────────────────────────

pub use z3_sys::Z3_inc_ref as inc_ref;
pub use z3_sys::Z3_dec_ref as dec_ref;

// ── AST inspection ──────────────────────────────────────────────────────

pub unsafe fn to_app(c: Context, a: Ast) -> App {
    unsafe { z3_sys::Z3_to_app(c, a).z3() }
}
pub unsafe fn get_app_decl(c: Context, a: App) -> FuncDecl {
    unsafe { z3_sys::Z3_get_app_decl(c, a).z3() }
}
pub use z3_sys::Z3_get_app_num_args as get_app_num_args;
pub unsafe fn get_app_arg(c: Context, a: App, i: u32) -> Ast {
    unsafe { z3_sys::Z3_get_app_arg(c, a, i).z3() }
}
pub use z3_sys::Z3_get_decl_kind as get_decl_kind;
pub unsafe fn get_decl_name(c: Context, d: FuncDecl) -> Symbol {
    unsafe { z3_sys::Z3_get_decl_name(c, d).z3() }
}
pub use z3_sys::Z3_get_decl_int_parameter as get_decl_int_parameter;
pub use z3_sys::Z3_get_ast_kind as get_ast_kind;
pub unsafe fn get_sort(c: Context, a: Ast) -> Sort {
    unsafe { z3_sys::Z3_get_sort(c, a).z3() }
}
pub use z3_sys::Z3_get_sort_kind as get_sort_kind;
pub use z3_sys::Z3_get_bv_sort_size as get_bv_sort_size;
pub use z3_sys::Z3_get_numeral_string as get_numeral_string;
pub use z3_sys::Z3_get_numeral_int as get_numeral_int;
pub use z3_sys::Z3_get_numeral_double as get_numeral_double;
pub use z3_sys::Z3_get_symbol_string as get_symbol_string;
pub use z3_sys::Z3_is_string as is_string;
pub use z3_sys::Z3_get_string as get_string;

pub unsafe fn simplify(c: Context, a: Ast) -> Ast {
    unsafe { z3_sys::Z3_simplify(c, a).z3() }
}

pub use z3_sys::Z3_func_decl_to_string as func_decl_to_string;

// ── FPA sort inspection ─────────────────────────────────────────────────

pub use z3_sys::Z3_fpa_get_ebits as fpa_get_ebits;
pub use z3_sys::Z3_fpa_get_sbits as fpa_get_sbits;
