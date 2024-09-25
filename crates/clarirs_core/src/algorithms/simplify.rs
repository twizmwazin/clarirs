use std::sync::Arc;

use crate::{algorithms::simplify, prelude::*};

pub trait Simplify<'c> {
    fn simplify(&self) -> Result<AstRef<'c>, ClarirsError>;
}

impl<'c> Simplify<'c> for AstRef<'c> {
    fn simplify(&self) -> Result<AstRef<'c>, ClarirsError> {
        simplify(self)
    }
}

pub fn simplify<'c>(ast: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    if let Some(ast) = ctx.simplification_cache.read()?.get(&ast.hash()) {
        if let Some(ast) = ast.upgrade() {
            return Ok(ast);
        }
    }

    macro_rules! simplify {
        ($($var:ident),*) => {
            $(let $var = simplify(&$var)?;)*
        };
    }

    let ast: AstRef = match &ast.op() {
        AstOp::BoolS(..)
        | AstOp::BoolV(..)
        | AstOp::BVS(..)
        | AstOp::BVV(..)
        | AstOp::SI(..)
        | AstOp::FPS(..)
        | AstOp::FPV(..)
        | AstOp::StringS(..)
        | AstOp::StringV(..) => ast.clone(),
        AstOp::Not(ast) => {
            simplify!(ast);
            match &ast.op() {
                AstOp::Not(ast) => ast.clone(),
                AstOp::BoolV(v) => ctx.boolv(!v)?,
                AstOp::BVV(v) => ctx.bvv(!v.clone())?,
                _ => ctx.not(&ast)?,
            }
        }
        AstOp::And(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BoolV(lhs), AstOp::BoolV(rhs)) => ctx.boolv(*lhs && *rhs)?,
                (AstOp::BoolV(true), v) | (v, AstOp::BoolV(true)) => ctx.make_ast(v.clone())?,
                (AstOp::BoolV(false), _) | (_, AstOp::BoolV(false)) => ctx.false_()?,
                (AstOp::Not(lhs), AstOp::Not(rhs)) => ctx.not(&ctx.or(lhs, rhs)?)?,
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() & rhs.clone())?,
                _ => ctx.and(&lhs, &rhs)?,
            }
        }
        AstOp::Or(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BoolV(lhs), AstOp::BoolV(rhs)) => ctx.boolv(*lhs || *rhs)?,
                (AstOp::BoolV(true), _) | (_, AstOp::BoolV(true)) => ctx.true_()?,
                (AstOp::BoolV(false), v) | (v, AstOp::BoolV(false)) => ctx.make_ast(v.clone())?,
                (AstOp::Not(lhs), AstOp::Not(rhs)) => ctx.not(&ctx.and(lhs, rhs)?)?,
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() | rhs.clone())?,
                _ => ctx.or(&lhs, &rhs)?,
            }
        }
        AstOp::Xor(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BoolV(lhs), AstOp::BoolV(rhs)) => ctx.boolv(*lhs ^ *rhs)?,
                (AstOp::BoolV(true), v) | (v, AstOp::BoolV(true)) => {
                    ctx.not(&ctx.make_ast(v.clone())?)?
                }
                (AstOp::BoolV(false), v) | (v, AstOp::BoolV(false)) => ctx.make_ast(v.clone())?,
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() ^ rhs.clone())?,
                _ => ctx.xor(&lhs, &rhs)?,
            }
        }
        AstOp::Add(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() + rhs.clone())?,
                _ => ctx.add(&lhs, &rhs)?,
            }
        }
        AstOp::Sub(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() - rhs.clone())?,
                _ => ctx.sub(&lhs, &rhs)?,
            }
        }
        AstOp::Mul(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() * rhs.clone())?,
                _ => ctx.mul(&lhs, &rhs)?,
            }
        }
        AstOp::UDiv(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() / rhs.clone())?,
                _ => ctx.udiv(&lhs, &rhs)?,
            }
        }
        AstOp::SDiv(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.sdiv(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.sdiv(&lhs, &rhs)?,
            }
        }
        AstOp::URem(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() % rhs.clone())?,
                _ => ctx.urem(&lhs, &rhs)?,
            }
        }
        AstOp::SRem(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.srem(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.srem(&lhs, &rhs)?,
            }
        }
        AstOp::Pow(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.pow(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.pow(&lhs, &rhs)?,
            }
        }
        AstOp::LShL(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.lshl(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.lshl(&lhs, &rhs)?,
            }
        }
        AstOp::LShR(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.lshr(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.lshl(&lhs, &rhs)?,
            }
        }
        AstOp::AShL(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.ashl(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.lshl(&lhs, &rhs)?,
            }
        }
        AstOp::AShR(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.ashr(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.lshl(&lhs, &rhs)?,
            }
        }
        AstOp::RotateLeft(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.rotate_left(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.rotate_left(&lhs, &rhs)?,
            }
        }
        AstOp::RotateRight(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.rotate_right(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.rotate_right(&lhs, &rhs)?,
            }
        }
        AstOp::ZeroExt(lhs, width) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::BVV(v) => ctx.zero_ext(&ctx.bvv(v.clone())?, *width)?,
                _ => ctx.zero_ext(&lhs, *width)?,
            }
        }
        AstOp::SignExt(lhs, width) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::BVV(v) => ctx.sign_ext(&ctx.bvv(v.clone())?, *width)?,
                _ => ctx.sign_ext(&lhs, *width)?,
            }
        }
        AstOp::Extract(lhs, lower, upper) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::BVV(v) => ctx.extract(&ctx.bvv(v.clone())?, *lower, *upper)?,
                _ => ctx.extract(&lhs, *lower, *upper)?,
            }
        }
        AstOp::Concat(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => {
                    ctx.concat(&ctx.bvv(lhs.clone())?, &ctx.bvv(rhs.clone())?)?
                }
                _ => ctx.concat(&lhs, &rhs)?,
            }
        }
        AstOp::Reverse(ast) => {
            simplify!(ast);
            match &ast.op() {
                AstOp::BVV(v) => ctx.bvv(v.clone().reverse())?,
                AstOp::Reverse(ast) => ast.clone(),
                _ => ctx.reverse(&ast)?,
            }
        }
        AstOp::Eq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs == rhs)?,
                _ => ctx.eq_(&lhs, &rhs)?,
            }
        }
        AstOp::Neq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs != rhs)?,
                _ => ctx.neq(&lhs, &rhs)?,
            }
        }
        AstOp::ULT(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs < rhs)?,
                _ => ctx.ult(&lhs, &rhs)?,
            }
        }
        AstOp::ULE(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs <= rhs)?,
                _ => ctx.ule(&lhs, &rhs)?,
            }
        }
        AstOp::UGT(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs > rhs)?,
                _ => ctx.ugt(&lhs, &rhs)?,
            }
        }
        AstOp::UGE(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs >= rhs)?,
                _ => ctx.uge(&lhs, &rhs)?,
            }
        }
        AstOp::SLT(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs < rhs)?,
                _ => ctx.slt(&lhs, &rhs)?,
            }
        }
        AstOp::SLE(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs <= rhs)?,
                _ => ctx.sle(&lhs, &rhs)?,
            }
        }
        AstOp::SGT(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs > rhs)?,
                _ => ctx.sgt(&lhs, &rhs)?,
            }
        }
        AstOp::SGE(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs >= rhs)?,
                _ => ctx.sge(&lhs, &rhs)?,
            }
        }
        AstOp::FpToFp(lhs, sort) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_to_fp(&ctx.fpv(v.clone())?, sort.clone())?,
                _ => ctx.fp_to_fp(&lhs, sort.clone())?,
            }
        }

        AstOp::BvToFpUnsigned(lhs, sort, rm) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::BVV(v) => {
                    ctx.bv_to_fp_unsigned(&ctx.bvv(v.clone())?, sort.clone(), rm.clone())?
                }
                _ => ctx.bv_to_fp_unsigned(&lhs, sort.clone(), rm.clone())?,
            }
        }
        AstOp::FpToIEEEBV(lhs) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_to_ieeebv(&ctx.fpv(v.clone())?)?,
                _ => ctx.fp_to_ieeebv(&lhs)?,
            }
        }
        AstOp::FpToUBV(lhs, width, rm) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_to_ubv(&ctx.fpv(v.clone())?, width.clone(), rm.clone())?,
                _ => ctx.fp_to_ubv(&lhs, width.clone(), rm.clone())?,
            }
        }
        AstOp::FpToSBV(lhs, width, rm) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_to_ubv(&ctx.fpv(v.clone())?, width.clone(), rm.clone())?,
                _ => ctx.fp_to_ubv(&lhs, width.clone(), rm.clone())?,
            }
        }
        AstOp::FpNeg(lhs, rm) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_neg(&ctx.fpv(v.clone())?, rm.clone())?,
                _ => ctx.fp_neg(&lhs, rm.clone())?,
            }
        }
        AstOp::FpAbs(lhs, rm) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_abs(&ctx.fpv(v.clone())?, rm.clone())?,
                _ => ctx.fp_abs(&lhs, rm.clone())?,
            }
        }
        AstOp::FpAdd(lhs, rhs, rm) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_add(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?, rm.clone())?
                }
                _ => ctx.fp_add(&lhs, &rhs, rm.clone())?,
            }
        }
        AstOp::FpSub(lhs, rhs, rm) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_sub(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?, rm.clone())?
                }
                _ => ctx.fp_sub(&lhs, &rhs, rm.clone())?,
            }
        }
        AstOp::FpMul(lhs, rhs, rm) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_mul(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?, rm.clone())?
                }
                _ => ctx.fp_mul(&lhs, &rhs, rm.clone())?,
            }
        }
        AstOp::FpDiv(lhs, rhs, rm) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_div(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?, rm.clone())?
                }
                _ => ctx.fp_div(&lhs, &rhs, rm.clone())?,
            }
        }
        AstOp::FpSqrt(lhs, rm) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::FPV(v) => ctx.fp_sqrt(&ctx.fpv(v.clone())?, rm.clone())?,
                _ => ctx.fp_sqrt(&lhs, rm.clone())?,
            }
        }
        AstOp::FpEq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => ctx.boolv(lhs == rhs)?,
                _ => ctx.fp_eq(&lhs, &rhs)?,
            }
        }
        AstOp::FpNeq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => ctx.boolv(lhs != rhs)?,
                _ => ctx.fp_neq(&lhs, &rhs)?,
            }
        }
        AstOp::FpLt(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_lt(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?)?
                }
                _ => ctx.fp_lt(&lhs, &rhs)?,
            }
        }
        AstOp::FpLeq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_leq(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?)?
                }
                _ => ctx.fp_leq(&lhs, &rhs)?,
            }
        }
        AstOp::FpGt(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_gt(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?)?
                }
                _ => ctx.fp_gt(&lhs, &rhs)?,
            }
        }
        AstOp::FpGeq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::FPV(lhs), AstOp::FPV(rhs)) => {
                    ctx.fp_geq(&ctx.fpv(lhs.clone())?, &ctx.fpv(rhs.clone())?)?
                }
                _ => ctx.fp_geq(&lhs, &rhs)?,
            }
        }
        AstOp::FpIsNan(ast) => {
            simplify!(ast);
            match ast.op() {
                AstOp::FPV(v) => ctx.fp_is_nan(&ctx.fpv(v.clone())?)?,
                _ => ctx.fp_is_nan(&ast)?,
            }
        }
        AstOp::FpIsInf(ast) => {
            simplify!(ast);
            match ast.op() {
                AstOp::FPV(v) => ctx.fp_is_inf(&ctx.fpv(v.clone())?)?,
                _ => ctx.fp_is_nan(&ast)?,
            }
        }
        AstOp::StrLen(lhs, bitlength) => {
            simplify!(lhs);
            match (lhs.op(), bitlength.op()) {
                (AstOp::StringV(v), AstOp::BVV(bitlength)) => {
                    ctx.strlen(&ctx.stringv(v.clone())?, &ctx.bvv(bitlength.clone())?)?
                }
                _ => ctx.strlen(&lhs, &bitlength)?,
            }
        }
        AstOp::StrConcat(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs)) => {
                    ctx.strconcat(&ctx.stringv(lhs.clone())?, &ctx.stringv(rhs.clone())?)?
                }
                _ => ctx.strconcat(&lhs, &rhs)?,
            }
        }
        AstOp::StrSubstr(start, end, lhs) => {
            simplify!(start, end, lhs);
            match (start.op(), end.op(), lhs.op()) {
                (AstOp::BVV(start), AstOp::BVV(end), AstOp::StringV(lhs)) => ctx.strsubstr(
                    &ctx.bvv(start.clone())?,
                    &ctx.bvv(end.clone())?,
                    &ctx.stringv(lhs.clone())?,
                )?,
                _ => ctx.strsubstr(&start, &end, &lhs)?,
            }
        }
        AstOp::StrContains(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs)) => {
                    ctx.strcontains(&ctx.stringv(lhs.clone())?, &ctx.stringv(rhs.clone())?)?
                }
                _ => ctx.strcontains(&lhs, &rhs)?,
            }
        }
        AstOp::StrIndexOf(lhs, start) => {
            simplify!(lhs, start);
            match (lhs.op(), start.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(start)) => {
                    ctx.strindexof(&ctx.stringv(lhs.clone())?, &ctx.stringv(start.clone())?)?
                }
                _ => ctx.strindexof(&lhs, &start)?,
            }
        }
        AstOp::StrReplace(lhs, rhs, start) => {
            simplify!(lhs, rhs, start);
            match (lhs.op(), rhs.op(), start.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs), AstOp::BVV(start)) => ctx.strreplace(
                    &ctx.stringv(lhs.clone())?,
                    &ctx.stringv(rhs.clone())?,
                    &ctx.bvv(start.clone())?,
                )?,
                _ => ctx.strreplace(&lhs, &rhs, &start)?,
            }
        }
        AstOp::StrPrefixOf(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs)) => {
                    ctx.strprefixof(&ctx.stringv(lhs.clone())?, &ctx.stringv(rhs.clone())?)?
                }
                _ => ctx.strprefixof(&lhs, &rhs)?,
            }
        }
        AstOp::StrSuffixOf(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs)) => {
                    ctx.strsuffixof(&ctx.stringv(lhs.clone())?, &ctx.stringv(rhs.clone())?)?
                }
                _ => ctx.strsuffixof(&lhs, &rhs)?,
            }
        }
        AstOp::StrToBV(lhs, width) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::StringV(v) => ctx.strtobv(&ctx.stringv(v.clone())?, &width)?,
                _ => ctx.strtobv(&lhs, &width)?,
            }
        }
        AstOp::BVToStr(lhs) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::BVV(v) => ctx.bvtostr(&ctx.bvv(v.clone())?)?,
                _ => ctx.bvtostr(&lhs)?,
            }
        }
        AstOp::StrIsDigit(lhs) => {
            simplify!(lhs);
            match lhs.op() {
                AstOp::StringV(v) => ctx.strisdigit(&ctx.stringv(v.clone())?)?,
                _ => ctx.strisdigit(&lhs)?,
            }
        }
        AstOp::StrEq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs)) => ctx.boolv(lhs == rhs)?,
                _ => ctx.streq(&lhs, &rhs)?,
            }
        }
        AstOp::StrNeq(lhs, rhs) => {
            simplify!(lhs, rhs);
            match (lhs.op(), rhs.op()) {
                (AstOp::StringV(lhs), AstOp::StringV(rhs)) => ctx.boolv(lhs != rhs)?,
                _ => ctx.strneq(&lhs, &rhs)?,
            }
        }
        AstOp::If(cond, then, else_) => {
            simplify!(cond, then, else_);
            match &cond.op() {
                AstOp::BoolV(true) => then.clone(),
                AstOp::BoolV(false) => else_.clone(),
                _ => ctx.if_(&cond, &then, &else_)?,
            }
        }
        AstOp::Annotated(ast, anno) => {
            simplify!(ast);
            if anno.eliminatable() {
                ast.clone()
            } else {
                ctx.annotated(&ast, anno.clone())?
            }
        }
    };

    ctx.simplification_cache
        .write()?
        .insert(ast.hash(), Arc::downgrade(&ast));
    Ok(ast)
}
