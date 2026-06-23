use std::ffi::CStr;

use ::z3 as z3hl;
use clarirs_core::{algorithms::walk_post_order, prelude::*};
use regex::Regex;
use z3_sys as z3;
use z3hl::ast::{Ast as _, BV, Bool, Dynamic, Int, RoundingMode};

use crate::{Z3_AST_CACHE, Z3_CONTEXT, check_z3_error, z3ext::wrap_ast};

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;
#[cfg(test)]
mod test_float;
#[cfg(test)]
mod test_string;

fn child(children: &[Dynamic], index: usize) -> Result<&Dynamic, ClarirsError> {
    children
        .get(index)
        .ok_or(ClarirsError::InvalidArguments(format!(
            "missing child at index {index}"
        )))
}

/// The `index`th Z3 child of `ast`, erroring if it is out of range.
fn nth(ast: &Dynamic, index: usize) -> Result<Dynamic, ClarirsError> {
    ast.nth_child(index)
        .ok_or_else(|| ClarirsError::ConversionError(format!("missing child at index {index}")))
}

// Typed downcasts of a converted child. The clarirs AST is type-checked before
// conversion, so a wrong sort here indicates an internal bug, surfaced as a
// conversion error rather than a panic.

fn as_bool(ast: &Dynamic) -> Result<Bool, ClarirsError> {
    ast.as_bool()
        .ok_or_else(|| ClarirsError::ConversionError("expected a boolean operand".to_string()))
}

fn as_bv(ast: &Dynamic) -> Result<BV, ClarirsError> {
    ast.as_bv()
        .ok_or_else(|| ClarirsError::ConversionError("expected a bitvector operand".to_string()))
}

fn as_int(ast: &Dynamic) -> Result<Int, ClarirsError> {
    ast.as_int()
        .ok_or_else(|| ClarirsError::ConversionError("expected an integer operand".to_string()))
}

fn as_float(ast: &Dynamic) -> Result<z3hl::ast::Float, ClarirsError> {
    ast.as_float().ok_or_else(|| {
        ClarirsError::ConversionError("expected a floating-point operand".to_string())
    })
}

fn as_string(ast: &Dynamic) -> Result<z3hl::ast::String, ClarirsError> {
    ast.as_string()
        .ok_or_else(|| ClarirsError::ConversionError("expected a string operand".to_string()))
}

// Build a Z3 node by downcasting the converted children to a typed sort and
// calling the matching high-level `z3` method, wrapping the result back into a
// [`Dynamic`]. `$cast` selects the operand sort (`as_bv`/`as_bool`/`as_float`).

macro_rules! unop {
    ($children:ident, $cast:ident, $method:ident) => {
        Dynamic::from_ast(&$cast(child($children, 0)?)?.$method())
    };
}

macro_rules! binop {
    ($children:ident, $cast:ident, $method:ident) => {{
        let a = $cast(child($children, 0)?)?;
        let b = $cast(child($children, 1)?)?;
        Dynamic::from_ast(&a.$method(b))
    }};
}

macro_rules! naryop {
    ($children:ident, $cast:ident, $method:ident) => {{
        let mut acc = $cast(child($children, 0)?)?;
        for i in 1..$children.len() {
            acc = acc.$method($cast(child($children, i)?)?);
        }
        Dynamic::from_ast(&acc)
    }};
}

/// Binary floating-point op taking a rounding mode (`fp.add`, `fp.div`, ...).
macro_rules! fp_rm_binop {
    ($children:ident, $method:ident, $rm:expr) => {{
        let a = as_float(child($children, 0)?)?;
        let b = as_float(child($children, 1)?)?;
        Dynamic::from_ast(&a.$method(b, &fprm_to_rm($rm)))
    }};
}

// Conversion helpers shared by the to_z3/from_z3 implementations.

/// The high-level [`RoundingMode`] for a clarirs [`FPRM`].
fn fprm_to_rm(rm: FPRM) -> RoundingMode {
    match rm {
        FPRM::NearestTiesToEven => RoundingMode::round_nearest_ties_to_even(),
        FPRM::TowardPositive => RoundingMode::round_towards_positive(),
        FPRM::TowardNegative => RoundingMode::round_towards_negative(),
        FPRM::TowardZero => RoundingMode::round_towards_zero(),
        FPRM::NearestTiesToAway => RoundingMode::round_nearest_ties_to_away(),
    }
}

/// The Z3 floating-point sort for `sort`, as a reference-counted handle. Z3's
/// sbits includes the implicit leading bit, so `mantissa + 1` is passed. The
/// caller must keep the returned [`z3hl::Sort`] alive while building a node from
/// it (`.get_z3_sort()`), since sorts are GC'd in the crate's rc context.
fn fsort_to_z3(sort: FSort) -> z3hl::Sort {
    z3hl::Sort::float(sort.exponent, sort.mantissa + 1)
}

/// The clarirs [`FSort`] for a Z3 floating-point [`z3hl::Sort`]. Z3's sbits
/// includes the implicit leading bit, so 1 is subtracted for the mantissa.
fn fsort_from_z3(sort: &z3hl::Sort) -> FSort {
    FSort::new(
        sort.float_exponent_size().unwrap(),
        sort.float_significand_size().unwrap() - 1,
    )
}

fn parse_fprm_from_z3(ast: &Dynamic) -> Result<FPRM, ClarirsError> {
    match ast.decl().kind() {
        z3::DeclKind::FpaRmNearestTiesToEven => Ok(FPRM::NearestTiesToEven),
        z3::DeclKind::FpaRmTowardPositive => Ok(FPRM::TowardPositive),
        z3::DeclKind::FpaRmTowardNegative => Ok(FPRM::TowardNegative),
        z3::DeclKind::FpaRmTowardZero => Ok(FPRM::TowardZero),
        z3::DeclKind::FpaRmNearestTiesToAway => Ok(FPRM::NearestTiesToAway),
        _ => Err(ClarirsError::ConversionError(
            "Unknown rounding mode".to_string(),
        )),
    }
}

/// Read a Z3 numeral as a decimal string. The `z3` crate only exposes 64-bit
/// numeral accessors (`as_u64`/`as_i64`), so arbitrary-width bitvector and
/// float values still go through the C API.
fn numeral_string(ast: &Dynamic) -> String {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        CStr::from_ptr(z3::Z3_get_numeral_string(z3_ctx, ast.get_z3_ast()))
            .to_str()
            .unwrap()
            .to_string()
    })
}

/// Read the `index`th integer parameter of `ast`'s declaration (e.g. the
/// high/low bounds of an `extract`). The `z3` crate's `FuncDecl` exposes no
/// parameter accessor, so this stays on the C API.
fn decl_int_parameter(ast: &Dynamic, index: u32) -> u32 {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        let app = z3::Z3_to_app(z3_ctx, ast.get_z3_ast()).unwrap();
        let decl = z3::Z3_get_app_decl(z3_ctx, app).unwrap();
        z3::Z3_get_decl_int_parameter(z3_ctx, decl, index) as u32
    })
}

/// The width of a bitvector-sorted `ast`, read through the C API. Used where
/// the operand sort is not statically known to be a bitvector, to preserve the
/// original behavior exactly.
fn bv_sort_size(ast: &Dynamic) -> u32 {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        z3::Z3_get_bv_sort_size(z3_ctx, z3::Z3_get_sort(z3_ctx, ast.get_z3_ast()).unwrap())
    })
}

/// Whether `ast` is a Z3 string literal. The `z3` crate exposes no predicate for
/// this — its `as_string` only checks the sort, and Z3 yields a spurious empty
/// string for non-literal string expressions — so use the C API.
fn is_string_literal(ast: &Dynamic) -> bool {
    Z3_CONTEXT.with(|&z3_ctx| unsafe { z3::Z3_is_string(z3_ctx, ast.get_z3_ast()) })
}

fn decode_custom_unicode(input: &str) -> String {
    let re = Regex::new(r"\\u\{([0-9a-fA-F]+)\}").unwrap();
    re.replace_all(input, |caps: &regex::Captures| {
        let num = u32::from_str_radix(&caps[1], 16).unwrap();
        std::char::from_u32(num).unwrap().to_string()
    })
    .into_owned()
}

pub(crate) trait AstExtZ3<'c>: HasContext<'c> + Sized {
    fn to_z3(&self) -> Result<Dynamic, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<Dynamic>) -> Result<Self, ClarirsError>;
    fn simplify_z3(&self) -> Result<Self, ClarirsError>;
}

impl<'c> AstExtZ3<'c> for AstRef<'c> {
    fn simplify_z3(&self) -> Result<Self, ClarirsError> {
        let simplified = self.simplify()?.to_z3()?.simplify();
        Self::from_z3(self.context(), simplified)
    }

    fn to_z3(&self) -> Result<Dynamic, ClarirsError> {
        // Builds a Z3 AST for a single node given its already-converted
        // children. A single match over the unified op enum handles all sorts;
        // polymorphic ops (Not/And/Or/Xor) pick the boolean or bitvector
        // builder from the node's type. Operations are built through the
        // high-level `z3` crate, falling back to `z3-sys` only where the crate
        // has no equivalent (flagged inline).
        Z3_AST_CACHE.with(|cache| {
            walk_post_order(
                self.clone(),
                |ast, children| {
                    Z3_CONTEXT.with(|&z3_ctx| unsafe {
                        Ok(match ast.op() {
                            // Polymorphic boolean/bitvector operations
                            AstOp::Not(..) => {
                                if ast.ast_type().is_bool() {
                                    unop!(children, as_bool, not)
                                } else {
                                    unop!(children, as_bv, bvnot)
                                }
                            }
                            AstOp::And(..) => {
                                if ast.ast_type().is_bool() {
                                    let args =
                                        children.iter().map(as_bool).collect::<Result<Vec<_>, _>>()?;
                                    Dynamic::from_ast(&Bool::and(&args))
                                } else {
                                    naryop!(children, as_bv, bvand)
                                }
                            }
                            AstOp::Or(..) => {
                                if ast.ast_type().is_bool() {
                                    let args =
                                        children.iter().map(as_bool).collect::<Result<Vec<_>, _>>()?;
                                    Dynamic::from_ast(&Bool::or(&args))
                                } else {
                                    naryop!(children, as_bv, bvor)
                                }
                            }
                            AstOp::Xor(..) => {
                                if ast.ast_type().is_bool() {
                                    naryop!(children, as_bool, xor)
                                } else {
                                    naryop!(children, as_bv, bvxor)
                                }
                            }
                            AstOp::ITE(..) => {
                                let cond = as_bool(child(children, 0)?)?;
                                cond.ite(child(children, 1)?, child(children, 2)?)
                            }

                            // Boolean leaves and predicates
                            AstOp::BoolS(s) => Dynamic::from_ast(&Bool::new_const(s.as_str())),
                            AstOp::BoolV(b) => Dynamic::from_ast(&Bool::from_bool(*b)),
                            // Equality (any sort): floats use fp.eq, everything else structural =.
                            AstOp::Eq(a, _) => {
                                if a.ast_type().is_float() {
                                    binop!(children, as_float, eq_fpa)
                                } else {
                                    let lhs = child(children, 0)?;
                                    let rhs = child(children, 1)?;
                                    Dynamic::from_ast(&lhs.eq(rhs.clone()))
                                }
                            }
                            AstOp::Neq(a, _) => {
                                if a.ast_type().is_float() {
                                    // IEEE inequality. Z3's `distinct` on floats is object
                                    // identity (NaN would equal NaN, +0 would differ from -0),
                                    // so emit not(fp.eq) instead.
                                    let eq = as_float(child(children, 0)?)?
                                        .eq_fpa(as_float(child(children, 1)?)?);
                                    Dynamic::from_ast(&eq.not())
                                } else {
                                    Dynamic::from_ast(&Dynamic::distinct(&[
                                        child(children, 0)?,
                                        child(children, 1)?,
                                    ]))
                                }
                            }
                            AstOp::ULT(..) => binop!(children, as_bv, bvult),
                            AstOp::ULE(..) => binop!(children, as_bv, bvule),
                            AstOp::UGT(..) => binop!(children, as_bv, bvugt),
                            AstOp::UGE(..) => binop!(children, as_bv, bvuge),
                            AstOp::SLT(..) => binop!(children, as_bv, bvslt),
                            AstOp::SLE(..) => binop!(children, as_bv, bvsle),
                            AstOp::SGT(..) => binop!(children, as_bv, bvsgt),
                            AstOp::SGE(..) => binop!(children, as_bv, bvsge),
                            AstOp::FpLt(..) => binop!(children, as_float, lt),
                            AstOp::FpLeq(..) => binop!(children, as_float, le),
                            AstOp::FpGt(..) => binop!(children, as_float, gt),
                            AstOp::FpGeq(..) => binop!(children, as_float, ge),
                            AstOp::FpIsNan(..) => unop!(children, as_float, is_nan),
                            AstOp::FpIsInf(..) => unop!(children, as_float, is_infinite),
                            AstOp::StrContains(..) => binop!(children, as_string, contains),
                            AstOp::StrPrefixOf(..) => binop!(children, as_string, prefix),
                            AstOp::StrSuffixOf(..) => binop!(children, as_string, suffix),
                            AstOp::StrIsDigit(..) => {
                                let s = as_string(child(children, 0)?)?;
                                // str.to_int returns -1 for non-digit strings, so >= 0 with a
                                // non-empty string means all digits. The `z3` crate has no
                                // str.to_int wrapper, so build it through the C API.
                                let int_val =
                                    as_int(&wrap_ast(z3::Z3_mk_str_to_int(z3_ctx, s.get_z3_ast()))?)?;
                                let is_non_negative = int_val.ge(Int::from_i64(0));
                                let is_non_empty = s.length().gt(Int::from_i64(0));
                                Dynamic::from_ast(&Bool::and(&[is_non_negative, is_non_empty]))
                            }

                            // Bitvector leaves and operations
                            AstOp::BVS(s, w) => Dynamic::from_ast(&BV::new_const(s.as_str(), *w)),
                            AstOp::BVV(v) => {
                                let numeral = v.to_biguint().to_string();
                                Dynamic::from_ast(&BV::from_str(v.len(), &numeral).ok_or_else(
                                    || {
                                        ClarirsError::ConversionError(
                                            "failed to build Z3 bitvector numeral".to_string(),
                                        )
                                    },
                                )?)
                            }
                            AstOp::Neg(..) => unop!(children, as_bv, bvneg),
                            AstOp::Add(..) => naryop!(children, as_bv, bvadd),
                            AstOp::Sub(..) => binop!(children, as_bv, bvsub),
                            AstOp::Mul(..) => naryop!(children, as_bv, bvmul),
                            AstOp::UDiv(..) => binop!(children, as_bv, bvudiv),
                            AstOp::SDiv(..) => binop!(children, as_bv, bvsdiv),
                            AstOp::URem(..) => binop!(children, as_bv, bvurem),
                            AstOp::SRem(..) => binop!(children, as_bv, bvsrem),
                            AstOp::ShL(..) => binop!(children, as_bv, bvshl),
                            AstOp::LShR(..) => binop!(children, as_bv, bvlshr),
                            AstOp::AShR(..) => binop!(children, as_bv, bvashr),
                            AstOp::RotateLeft(..) => binop!(children, as_bv, bvrotl),
                            AstOp::RotateRight(..) => binop!(children, as_bv, bvrotr),
                            AstOp::ZeroExt(_, i) => {
                                Dynamic::from_ast(&as_bv(child(children, 0)?)?.zero_ext(*i))
                            }
                            AstOp::SignExt(_, i) => {
                                Dynamic::from_ast(&as_bv(child(children, 0)?)?.sign_ext(*i))
                            }
                            AstOp::Extract(a, high, low) => {
                                if high >= &a.size() || low >= &a.size() {
                                    return Err(ClarirsError::ConversionError(
                                        "extract index is greater than bitvector size".to_string(),
                                    ));
                                }
                                if low > high {
                                    return Err(ClarirsError::ConversionError(
                                        "low index is greater than high index".to_string(),
                                    ));
                                }
                                Dynamic::from_ast(&as_bv(child(children, 0)?)?.extract(*high, *low))
                            }
                            AstOp::Concat(args) => {
                                if args.is_empty() {
                                    return Err(ClarirsError::InvalidArguments(
                                        "Concat requires at least one argument".to_string(),
                                    ));
                                }
                                naryop!(children, as_bv, concat)
                            }
                            AstOp::ByteReverse(a) => {
                                let size = a.size();
                                if size == 0 || size % 8 != 0 {
                                    return Err(ClarirsError::ConversionError(
                                        "reverse only supports bitvectors with size multiple of 8"
                                            .to_string(),
                                    ));
                                }
                                let bv = as_bv(child(children, 0)?)?;
                                let mut acc = bv.extract(7, 0);
                                for i in 1..size / 8 {
                                    acc = acc.concat(bv.extract((i + 1) * 8 - 1, i * 8));
                                }
                                Dynamic::from_ast(&acc)
                            }
                            AstOp::FpToIEEEBV(..) => {
                                Dynamic::from_ast(&as_float(child(children, 0)?)?.to_ieee_bv())
                            }
                            AstOp::FpToUBV(_, size, rm) => Dynamic::from_ast(
                                &as_float(child(children, 0)?)?
                                    .to_ubv_with_rounding_mode(&fprm_to_rm(*rm), *size),
                            ),
                            AstOp::FpToSBV(_, size, rm) => Dynamic::from_ast(
                                &as_float(child(children, 0)?)?
                                    .to_sbv_with_rounding_mode(&fprm_to_rm(*rm), *size),
                            ),
                            AstOp::StrLen(..) => Dynamic::from_ast(&BV::from_int(
                                &as_string(child(children, 0)?)?.length(),
                                64,
                            )),
                            AstOp::StrIndexOf(..) => {
                                let haystack = as_string(child(children, 0)?)?;
                                let needle = as_string(child(children, 1)?)?;
                                let offset = as_bv(child(children, 2)?)?.to_int(false);
                                // The `z3` crate has no seq.index_of wrapper.
                                let index = wrap_ast(z3::Z3_mk_seq_index(
                                    z3_ctx,
                                    haystack.get_z3_ast(),
                                    needle.get_z3_ast(),
                                    offset.get_z3_ast(),
                                ))?;
                                Dynamic::from_ast(&BV::from_int(&as_int(&index)?, 64))
                            }
                            AstOp::StrToBV(..) => {
                                let s = as_string(child(children, 0)?)?;
                                // The `z3` crate has no str.to_int wrapper.
                                let int_val =
                                    wrap_ast(z3::Z3_mk_str_to_int(z3_ctx, s.get_z3_ast()))?;
                                Dynamic::from_ast(&BV::from_int(&as_int(&int_val)?, 64))
                            }
                            AstOp::Union(..) | AstOp::Intersection(..) | AstOp::Widen(..) => {
                                return Err(ClarirsError::ConversionError(
                                    "vsa types are not currently supported in the z3 backend"
                                        .to_string(),
                                ));
                            }

                            // Float leaves and operations
                            AstOp::FPS(s, sort) => Dynamic::from_ast(&z3hl::ast::Float::new_const(
                                s.as_str(),
                                sort.exponent,
                                sort.mantissa + 1,
                            )),
                            AstOp::FPV(f) => match f {
                                Float::F32(val) => {
                                    Dynamic::from_ast(&z3hl::ast::Float::from_f32(*val))
                                }
                                Float::F64(val) => {
                                    Dynamic::from_ast(&z3hl::ast::Float::from_f64(*val))
                                }
                            },
                            AstOp::FpNeg(..) => unop!(children, as_float, unary_neg),
                            AstOp::FpAbs(..) => unop!(children, as_float, unary_abs),
                            AstOp::FpAdd(_, _, rm) => {
                                fp_rm_binop!(children, add_with_rounding_mode, *rm)
                            }
                            AstOp::FpSub(_, _, rm) => {
                                fp_rm_binop!(children, sub_with_rounding_mode, *rm)
                            }
                            AstOp::FpMul(_, _, rm) => {
                                fp_rm_binop!(children, mul_with_rounding_mode, *rm)
                            }
                            AstOp::FpDiv(_, _, rm) => {
                                fp_rm_binop!(children, div_with_rounding_mode, *rm)
                            }
                            AstOp::FpSqrt(_, rm) => Dynamic::from_ast(
                                &as_float(child(children, 0)?)?
                                    .sqrt_with_rounding_mode(&fprm_to_rm(*rm)),
                            ),
                            AstOp::FpToFp(_, sort, rm) => Dynamic::from_ast(
                                &as_float(child(children, 0)?)?
                                    .to_fp_with_rounding_mode(&fprm_to_rm(*rm), &fsort_to_z3(*sort)),
                            ),
                            AstOp::FpFP(..) => {
                                // The `z3` crate has no constructor assembling a float from its
                                // sign/exponent/significand bitvectors.
                                wrap_ast(z3::Z3_mk_fpa_fp(
                                    z3_ctx,
                                    child(children, 0)?.get_z3_ast(),
                                    child(children, 1)?.get_z3_ast(),
                                    child(children, 2)?.get_z3_ast(),
                                ))?
                            }
                            AstOp::BvToFp(_, sort) => {
                                // The `z3` crate has no bitvector-to-float constructors.
                                let target = fsort_to_z3(*sort);
                                wrap_ast(z3::Z3_mk_fpa_to_fp_bv(
                                    z3_ctx,
                                    child(children, 0)?.get_z3_ast(),
                                    target.get_z3_sort(),
                                ))?
                            }
                            AstOp::BvToFpSigned(_, sort, rm) => {
                                let target = fsort_to_z3(*sort);
                                wrap_ast(z3::Z3_mk_fpa_to_fp_signed(
                                    z3_ctx,
                                    fprm_to_rm(*rm).get_z3_ast(),
                                    child(children, 0)?.get_z3_ast(),
                                    target.get_z3_sort(),
                                ))?
                            }
                            AstOp::BvToFpUnsigned(_, sort, rm) => {
                                let target = fsort_to_z3(*sort);
                                wrap_ast(z3::Z3_mk_fpa_to_fp_unsigned(
                                    z3_ctx,
                                    fprm_to_rm(*rm).get_z3_ast(),
                                    child(children, 0)?.get_z3_ast(),
                                    target.get_z3_sort(),
                                ))?
                            }

                            // String leaves and operations
                            AstOp::StringS(s) => {
                                Dynamic::from_ast(&z3hl::ast::String::new_const(s.as_str()))
                            }
                            AstOp::StringV(s) => {
                                let mut encoded = String::new();
                                for ch in s.chars() {
                                    if ch.is_ascii() {
                                        encoded.push(ch);
                                    } else {
                                        encoded.push_str(&format!("\\u{{{:04X}}}", ch as u32));
                                    }
                                }
                                Dynamic::from_ast(&z3hl::ast::String::from(encoded.as_str()))
                            }
                            AstOp::StrConcat(..) => {
                                let a = as_string(child(children, 0)?)?;
                                let b = as_string(child(children, 1)?)?;
                                Dynamic::from_ast(&z3hl::ast::String::concat(&[a, b]))
                            }
                            AstOp::StrSubstr(..) => {
                                let s = as_string(child(children, 0)?)?;
                                let offset = as_bv(child(children, 1)?)?.to_int(false);
                                let length = as_bv(child(children, 2)?)?.to_int(false);
                                Dynamic::from_ast(&s.substr(offset, length))
                            }
                            AstOp::StrReplace(..) => {
                                // The `z3` crate has no str.replace wrapper.
                                let a = as_string(child(children, 0)?)?;
                                let b = as_string(child(children, 1)?)?;
                                let c = as_string(child(children, 2)?)?;
                                wrap_ast(z3::Z3_mk_seq_replace(
                                    z3_ctx,
                                    a.get_z3_ast(),
                                    b.get_z3_ast(),
                                    c.get_z3_ast(),
                                ))?
                            }
                            AstOp::BVToStr(_) => {
                                let int_val = as_bv(child(children, 0)?)?.to_int(false);
                                // The `z3` crate has no int.to_str wrapper.
                                wrap_ast(z3::Z3_mk_int_to_str(z3_ctx, int_val.get_z3_ast()))?
                            }
                        })
                        .and_then(|maybe_null| {
                            check_z3_error()?;
                            Ok(maybe_null)
                        })
                    })
                },
                cache,
            )
        })
    }

    /// Converts a Z3 AST back into an [`AstRef`]. A single match over the Z3
    /// declaration kind replaces the previous per-sort `from_z3` functions; the
    /// few kinds that span sorts (`Ite`, uninterpreted constants, numerals) pick
    /// the result sort from the Z3 sort kind. Introspection goes through the
    /// high-level `z3` crate (`kind`/`decl`/`nth_child`/`get_sort`), falling back
    /// to `z3-sys` only for reads the crate does not expose (flagged inline).
    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<Dynamic>) -> Result<Self, ClarirsError> {
        let ast = ast.into();
        match ast.kind() {
            z3::AstKind::Numeral => {
                let sort = ast.get_sort();
                match sort.kind() {
                    z3::SortKind::Bv => {
                        let width = as_bv(&ast)?.get_size();
                        ctx.bvv(BitVec::try_from((numeral_string(&ast), width)).unwrap())
                    }
                    z3::SortKind::FloatingPoint => {
                        let fsort = fsort_from_z3(&sort);
                        let numeral_str = numeral_string(&ast);
                        if fsort == FSort::f32() {
                            let val = numeral_str.parse::<f32>().map_err(|_| {
                                ClarirsError::ConversionError("Failed to parse f32".to_string())
                            })?;
                            ctx.fpv(Float::F32(val))
                        } else {
                            let val = numeral_str.parse::<f64>().map_err(|_| {
                                ClarirsError::ConversionError("Failed to parse float".to_string())
                            })?;
                            ctx.fpv(Float::F64(val))
                        }
                    }
                    _ => Err(ClarirsError::ConversionError(
                        "numeral has unsupported sort".to_string(),
                    )),
                }
            }
            z3::AstKind::App => {
                // String constants present as ordinary apps; catch them first.
                if is_string_literal(&ast) {
                    let value = ast.as_string().and_then(|s| s.as_string()).unwrap_or_default();
                    return ctx.stringv(decode_custom_unicode(&value));
                }

                let decl_kind = ast.decl().kind();
                let arg = |i: usize| nth(&ast, i);

                match decl_kind {
                    // Booleans
                    z3::DeclKind::True => ctx.true_(),
                    z3::DeclKind::False => ctx.false_(),
                    z3::DeclKind::Not => {
                        let inner = AstRef::from_z3(ctx, arg(0)?)?;
                        // Not(Eq(a, b)) canonicalizes to Neq(a, b).
                        if let AstOp::Eq(a, b) = inner.op() {
                            ctx.neq(a, b)
                        } else {
                            ctx.not(inner)
                        }
                    }
                    z3::DeclKind::And | z3::DeclKind::Or => {
                        let mut args = Vec::with_capacity(ast.num_children());
                        for i in 0..ast.num_children() {
                            args.push(AstRef::from_z3(ctx, arg(i)?)?);
                        }
                        match decl_kind {
                            z3::DeclKind::And => ctx.and(args),
                            _ => ctx.or(args),
                        }
                    }
                    z3::DeclKind::Xor => ctx.xor2(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Eq => {
                        let lhs = AstRef::from_z3(ctx, arg(0)?)?;
                        let rhs = AstRef::from_z3(ctx, arg(1)?)?;
                        // eq_ picks the right per-sort equality from the operand type.
                        ctx.eq_(lhs, rhs)
                    }
                    z3::DeclKind::Distinct => {
                        if ast.num_children() != 2 {
                            return Err(ClarirsError::ConversionError(
                                "Distinct with != 2 args not supported".to_string(),
                            ));
                        }
                        ctx.neq(
                            AstRef::from_z3(ctx, arg(0)?)?,
                            AstRef::from_z3(ctx, arg(1)?)?,
                        )
                    }
                    z3::DeclKind::Ult => ctx.ult(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Uleq => ctx.ule(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Ugt => ctx.ugt(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Ugeq => ctx.uge(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Slt => ctx.slt(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Sleq => ctx.sle(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Sgt => ctx.sgt(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Sgeq => ctx.sge(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::FpaEq => ctx.fp_eq(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::FpaLt => ctx.fp_lt(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::FpaLe => ctx.fp_leq(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::FpaGt => ctx.fp_gt(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::FpaGe => ctx.fp_geq(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::FpaIsNan => ctx.fp_is_nan(AstRef::from_z3(ctx, arg(0)?)?),
                    z3::DeclKind::FpaIsInf => ctx.fp_is_inf(AstRef::from_z3(ctx, arg(0)?)?),
                    z3::DeclKind::SeqContains => ctx.str_contains(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::SeqPrefix => ctx.str_prefix_of(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::SeqSuffix => ctx.str_suffix_of(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),

                    // Bitvectors
                    z3::DeclKind::Bnot => ctx.not(AstRef::from_z3(ctx, arg(0)?)?),
                    z3::DeclKind::Bneg => ctx.neg(AstRef::from_z3(ctx, arg(0)?)?),
                    z3::DeclKind::Band
                    | z3::DeclKind::Bor
                    | z3::DeclKind::Bxor
                    | z3::DeclKind::Badd
                    | z3::DeclKind::Bmul => {
                        let mut args = Vec::with_capacity(ast.num_children());
                        for i in 0..ast.num_children() {
                            args.push(AstRef::from_z3(ctx, arg(i)?)?);
                        }
                        match decl_kind {
                            z3::DeclKind::Band => ctx.and(args),
                            z3::DeclKind::Bor => ctx.or(args),
                            z3::DeclKind::Bxor => ctx.xor(args),
                            z3::DeclKind::Badd => ctx.add_many(args),
                            _ => ctx.mul_many(args),
                        }
                    }
                    z3::DeclKind::Bsub => ctx.sub(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Budiv => ctx.udiv(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Bsdiv => ctx.sdiv(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Burem => ctx.urem(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Bsrem => ctx.srem(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Bshl => ctx.shl(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Blshr => ctx.lshr(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::Bashr => ctx.ashr(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::ExtRotateLeft => ctx.rotate_left(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::ExtRotateRight => ctx.rotate_right(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::ZeroExt => {
                        let inner = AstRef::from_z3(ctx, arg(0)?)?;
                        ctx.zero_ext(inner, decl_int_parameter(&ast, 0))
                    }
                    z3::DeclKind::SignExt => {
                        let inner = AstRef::from_z3(ctx, arg(0)?)?;
                        ctx.sign_ext(inner, decl_int_parameter(&ast, 0))
                    }
                    z3::DeclKind::Extract => {
                        let inner = AstRef::from_z3(ctx, arg(0)?)?;
                        let high = decl_int_parameter(&ast, 0);
                        let low = decl_int_parameter(&ast, 1);
                        ctx.extract(inner, high, low)
                    }
                    z3::DeclKind::Concat => {
                        let mut args = Vec::with_capacity(ast.num_children());
                        for i in 0..ast.num_children() {
                            args.push(AstRef::from_z3(ctx, arg(i)?)?);
                        }
                        ctx.concat(args)
                    }
                    // int2bv wraps the string->bv operations and plain bv2int.
                    z3::DeclKind::Int2bv => {
                        let inner = arg(0)?;
                        match inner.kind() {
                            z3::AstKind::Numeral => {
                                // Preserve the original width read: the operand sort is not
                                // statically a bitvector, so go through the C API.
                                let width = bv_sort_size(&inner);
                                ctx.bvv(
                                    BitVec::try_from((numeral_string(&inner), width)).unwrap(),
                                )
                            }
                            z3::AstKind::App => match inner.decl().kind() {
                                z3::DeclKind::Bv2int => {
                                    AstRef::from_z3(ctx, nth(&inner, 0)?)
                                }
                                z3::DeclKind::SeqIndex => {
                                    let haystack = AstRef::from_z3(ctx, nth(&inner, 0)?)?;
                                    let needle = AstRef::from_z3(ctx, nth(&inner, 1)?)?;
                                    let off = as_int(&nth(&inner, 2)?)?;
                                    let offset = BV::from_int(&off, 64).simplify();
                                    ctx.str_index_of(
                                        haystack,
                                        needle,
                                        AstRef::from_z3(ctx, offset)?,
                                    )
                                }
                                z3::DeclKind::StrToInt => {
                                    ctx.str_to_bv(AstRef::from_z3(ctx, nth(&inner, 0)?)?)
                                }
                                z3::DeclKind::SeqLength => {
                                    ctx.str_len(AstRef::from_z3(ctx, nth(&inner, 0)?)?)
                                }
                                k => Err(ClarirsError::ConversionError(format!(
                                    "unexpected inner decl kind in Int2bv: {k:?}"
                                ))),
                            },
                            _ => Err(ClarirsError::ConversionError(
                                "expected a numeral or bv2int".to_string(),
                            )),
                        }
                    }

                    // Floats
                    z3::DeclKind::FpaNum => {
                        let fsort = fsort_from_z3(&ast.get_sort());
                        let val = as_float(&ast)?.as_f64();
                        if fsort == FSort::f32() {
                            ctx.fpv(Float::F32(val as f32))
                        } else {
                            ctx.fpv(Float::F64(val))
                        }
                    }
                    z3::DeclKind::FpaNan => {
                        let fsort = fsort_from_z3(&ast.get_sort());
                        if fsort == FSort::f32() {
                            ctx.fpv(Float::F32(f32::NAN))
                        } else {
                            ctx.fpv(Float::F64(f64::NAN))
                        }
                    }
                    z3::DeclKind::FpaNeg => ctx.fp_neg(AstRef::from_z3(ctx, arg(0)?)?),
                    z3::DeclKind::FpaAbs => ctx.fp_abs(AstRef::from_z3(ctx, arg(0)?)?),
                    z3::DeclKind::FpaAdd
                    | z3::DeclKind::FpaSub
                    | z3::DeclKind::FpaMul
                    | z3::DeclKind::FpaDiv => {
                        let rm = parse_fprm_from_z3(&arg(0)?)?;
                        let a = AstRef::from_z3(ctx, arg(1)?)?;
                        let b = AstRef::from_z3(ctx, arg(2)?)?;
                        match decl_kind {
                            z3::DeclKind::FpaAdd => ctx.fp_add(a, b, rm),
                            z3::DeclKind::FpaSub => ctx.fp_sub(a, b, rm),
                            z3::DeclKind::FpaMul => ctx.fp_mul(a, b, rm),
                            _ => ctx.fp_div(a, b, rm),
                        }
                    }
                    z3::DeclKind::FpaSqrt => {
                        let rm = parse_fprm_from_z3(&arg(0)?)?;
                        ctx.fp_sqrt(AstRef::from_z3(ctx, arg(1)?)?, rm)
                    }
                    z3::DeclKind::FpaToFp => {
                        let fsort = fsort_from_z3(&ast.get_sort());
                        match ast.num_children() {
                            1 => ctx.bv_to_fp(AstRef::from_z3(ctx, arg(0)?)?, fsort),
                            2 => {
                                let rm = parse_fprm_from_z3(&arg(0)?)?;
                                let operand = arg(1)?;
                                match operand.get_sort().kind() {
                                    z3::SortKind::FloatingPoint => {
                                        ctx.fp_to_fp(AstRef::from_z3(ctx, operand)?, fsort, rm)
                                    }
                                    z3::SortKind::Bv => ctx.bv_to_fp_signed(
                                        AstRef::from_z3(ctx, operand)?,
                                        fsort,
                                        rm,
                                    ),
                                    _ => Err(ClarirsError::ConversionError(
                                        "FpaToFp: unexpected sort kind for operand".to_string(),
                                    )),
                                }
                            }
                            _ => Err(ClarirsError::ConversionError(
                                "Unexpected number of arguments for FpaToFp".to_string(),
                            )),
                        }
                    }
                    z3::DeclKind::FpaFp => {
                        let sign = AstRef::from_z3(ctx, arg(0)?)?;
                        let exp = AstRef::from_z3(ctx, arg(1)?)?;
                        let sig = AstRef::from_z3(ctx, arg(2)?)?;
                        ctx.fp_fp(sign, exp, sig)
                    }
                    z3::DeclKind::FpaToIeeeBv => ctx.fp_to_ieeebv(AstRef::from_z3(ctx, arg(0)?)?),
                    // Zero/infinity special values present as zero-argument
                    // apps, not numerals (e.g. in models: (_ -zero 8 24)).
                    // (FpaNan is handled above.)
                    z3::DeclKind::FpaPlusZero
                    | z3::DeclKind::FpaMinusZero
                    | z3::DeclKind::FpaPlusInf
                    | z3::DeclKind::FpaMinusInf => {
                        let fsort = fsort_from_z3(&ast.get_sort());
                        let val = match decl_kind {
                            z3::DeclKind::FpaPlusZero => 0.0f64,
                            z3::DeclKind::FpaMinusZero => -0.0f64,
                            z3::DeclKind::FpaPlusInf => f64::INFINITY,
                            _ => f64::NEG_INFINITY,
                        };
                        if fsort == FSort::f32() {
                            ctx.fpv(Float::F32(val as f32))
                        } else {
                            ctx.fpv(Float::F64(val))
                        }
                    }

                    // Strings
                    z3::DeclKind::SeqConcat => ctx.str_concat(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                    ),
                    z3::DeclKind::SeqExtract => {
                        let a = AstRef::from_z3(ctx, arg(0)?)?;
                        let offset = BV::from_int(&as_int(&arg(1)?)?, 64).simplify();
                        let length = BV::from_int(&as_int(&arg(2)?)?, 64).simplify();
                        ctx.str_substr(
                            a,
                            AstRef::from_z3(ctx, offset)?,
                            AstRef::from_z3(ctx, length)?,
                        )
                    }
                    z3::DeclKind::SeqReplace => ctx.str_replace(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                        AstRef::from_z3(ctx, arg(2)?)?,
                    ),
                    z3::DeclKind::IntToStr => {
                        // int.to.str(bv2int(bv)) -> BVToStr(bv)
                        let inner = arg(0)?;
                        if inner.decl().kind() == z3::DeclKind::Bv2int {
                            ctx.bv_to_str(AstRef::from_z3(ctx, nth(&inner, 0)?)?)
                        } else {
                            Err(ClarirsError::ConversionError(
                                "expected bv2int inside int_to_str".to_string(),
                            ))
                        }
                    }

                    // Shared across sorts
                    z3::DeclKind::Ite => ctx.ite(
                        AstRef::from_z3(ctx, arg(0)?)?,
                        AstRef::from_z3(ctx, arg(1)?)?,
                        AstRef::from_z3(ctx, arg(2)?)?,
                    ),
                    z3::DeclKind::Uninterpreted => {
                        let sort = ast.get_sort();
                        let name = ast.decl().name();
                        match sort.kind() {
                            z3::SortKind::Bool => ctx.bools(name),
                            z3::SortKind::Bv => ctx.bvs(name, as_bv(&ast)?.get_size()),
                            z3::SortKind::FloatingPoint => ctx.fps(name, fsort_from_z3(&sort)),
                            z3::SortKind::Seq => ctx.strings(name),
                            _ => Err(ClarirsError::ConversionError(
                                "uninterpreted constant has unsupported sort".to_string(),
                            )),
                        }
                    }
                    _ => Err(ClarirsError::ConversionError(format!(
                        "Failed converting from z3: unknown decl kind: {}",
                        ast.decl().name()
                    ))),
                }
            }
            _ => Err(ClarirsError::ConversionError(
                "Failed converting from z3: unknown ast kind".to_string(),
            )),
        }
    }
}
