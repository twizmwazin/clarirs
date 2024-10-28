use std::sync::Arc;

use crate::prelude::*;

macro_rules! simplify {
    ($($var:ident),*) => {
        $(let $var = simplify(&$var)?;)*
    };
}

pub trait Simplify<'c>: Sized {
    fn simplify(&self) -> Result<Self, ClarirsError>;
}

impl<'c> Simplify<'c> for BoolAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        Ok(self
            .context()
            .simplification_cache
            .get_or_insert_with_bool(self.hash(), || match &self.op() {
                BooleanOp::BoolS(_) => self.clone(),
                BooleanOp::BoolV(_) => self.clone(),
                BooleanOp::Not(arc) => todo!(),
                BooleanOp::And(arc, arc1) => todo!(),
                BooleanOp::Or(arc, arc1) => todo!(),
                BooleanOp::Xor(arc, arc1) => todo!(),
                BooleanOp::Eq(arc, arc1) => todo!(),
                BooleanOp::Neq(arc, arc1) => todo!(),
                BooleanOp::ULT(arc, arc1) => todo!(),
                BooleanOp::ULE(arc, arc1) => todo!(),
                BooleanOp::UGT(arc, arc1) => todo!(),
                BooleanOp::UGE(arc, arc1) => todo!(),
                BooleanOp::SLT(arc, arc1) => todo!(),
                BooleanOp::SLE(arc, arc1) => todo!(),
                BooleanOp::SGT(arc, arc1) => todo!(),
                BooleanOp::SGE(arc, arc1) => todo!(),
                BooleanOp::FpEq(arc, arc1) => todo!(),
                BooleanOp::FpNeq(arc, arc1) => todo!(),
                BooleanOp::FpLt(arc, arc1) => todo!(),
                BooleanOp::FpLeq(arc, arc1) => todo!(),
                BooleanOp::FpGt(arc, arc1) => todo!(),
                BooleanOp::FpGeq(arc, arc1) => todo!(),
                BooleanOp::FpIsNan(arc) => todo!(),
                BooleanOp::FpIsInf(arc) => todo!(),
                BooleanOp::StrContains(arc, arc1) => todo!(),
                BooleanOp::StrPrefixOf(arc, arc1) => todo!(),
                BooleanOp::StrSuffixOf(arc, arc1) => todo!(),
                BooleanOp::StrIsDigit(arc) => todo!(),
                BooleanOp::StrEq(arc, arc1) => todo!(),
                BooleanOp::StrNeq(arc, arc1) => todo!(),
                BooleanOp::If(arc, arc1, arc2) => todo!(),
                BooleanOp::Annotated(arc, annotation) => todo!(),
            }))
    }
}

impl<'c> Simplify<'c> for BitVecAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        Ok(self
            .context()
            .simplification_cache
            .get_or_insert_with_bv(self.hash(), || match &self.op() {
                BitVecOp::BVS(..) => self.clone(),
                BitVecOp::BVV(..) => self.clone(),
                BitVecOp::SI(..) => todo!(),
                BitVecOp::Not(ast) => todo!(),
                BitVecOp::And(arc, arc1) => todo!(),
                BitVecOp::Or(arc, arc1) => todo!(),
                BitVecOp::Xor(arc, arc1) => todo!(),
                BitVecOp::Add(arc, arc1) => todo!(),
                BitVecOp::Sub(arc, arc1) => todo!(),
                BitVecOp::Mul(arc, arc1) => todo!(),
                BitVecOp::UDiv(arc, arc1) => todo!(),
                BitVecOp::SDiv(arc, arc1) => todo!(),
                BitVecOp::URem(arc, arc1) => todo!(),
                BitVecOp::SRem(arc, arc1) => todo!(),
                BitVecOp::Pow(arc, arc1) => todo!(),
                BitVecOp::LShL(arc, arc1) => todo!(),
                BitVecOp::LShR(arc, arc1) => todo!(),
                BitVecOp::AShL(arc, arc1) => todo!(),
                BitVecOp::AShR(arc, arc1) => todo!(),
                BitVecOp::RotateLeft(arc, arc1) => todo!(),
                BitVecOp::RotateRight(arc, arc1) => todo!(),
                BitVecOp::ZeroExt(arc, _) => todo!(),
                BitVecOp::SignExt(arc, _) => todo!(),
                BitVecOp::Extract(arc, _, _) => todo!(),
                BitVecOp::Concat(arc, arc1) => todo!(),
                BitVecOp::Reverse(arc) => todo!(),
                BitVecOp::FpToIEEEBV(arc) => todo!(),
                BitVecOp::FpToUBV(arc, _, fprm) => todo!(),
                BitVecOp::FpToSBV(arc, _, fprm) => todo!(),
                BitVecOp::StrLen(arc) => todo!(),
                BitVecOp::StrIndexOf(arc, arc1, arc2) => todo!(),
                BitVecOp::StrToBV(arc) => todo!(),
                BitVecOp::If(arc, arc1, arc2) => todo!(),
                BitVecOp::Annotated(arc, annotation) => todo!(),
            }))
    }
}

impl<'c> Simplify<'c> for FloatAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        Ok(self
            .context()
            .simplification_cache
            .get_or_insert_with_float(self.hash(), || match &self.op() {
                FloatOp::FPS(_, fsort) => todo!(),
                FloatOp::FPV(float) => todo!(),
                FloatOp::FpNeg(arc, fprm) => todo!(),
                FloatOp::FpAbs(arc, fprm) => todo!(),
                FloatOp::FpAdd(arc, arc1, fprm) => todo!(),
                FloatOp::FpSub(arc, arc1, fprm) => todo!(),
                FloatOp::FpMul(arc, arc1, fprm) => todo!(),
                FloatOp::FpDiv(arc, arc1, fprm) => todo!(),
                FloatOp::FpSqrt(arc, fprm) => todo!(),
                FloatOp::FpToFp(arc, fsort, fprm) => todo!(),
                FloatOp::BvToFpUnsigned(arc, fsort, fprm) => todo!(),
                FloatOp::If(arc, arc1, arc2) => todo!(),
                FloatOp::Annotated(arc, annotation) => todo!(),
            }))
    }
}

impl<'c> Simplify<'c> for StringAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        Ok(self
            .context()
            .simplification_cache
            .get_or_insert_with_string(self.hash(), || match &self.op() {
                StringOp::StringS(_, _) => todo!(),
                StringOp::StringV(_) => todo!(),
                StringOp::StrConcat(arc, arc1) => todo!(),
                StringOp::StrSubstr(arc, arc1, arc2) => todo!(),
                StringOp::StrReplace(arc, arc1, arc2) => todo!(),
                StringOp::BVToStr(arc) => todo!(),
                StringOp::If(arc, arc1, arc2) => todo!(),
                StringOp::Annotated(arc, annotation) => todo!(),
            }))
    }
}

// pub fn simplify<'c>(ast: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
//     let ctx = ast.context();

//     if let Some(ast) = ctx.simplification_cache.read()?.get(&ast.hash()) {
//         if let Some(ast) = ast.upgrade() {
//             return Ok(ast);
//         }
//     }

//     let ast: AstRef = match &ast.op() {
//         AstOp::BoolS(..)
//         | AstOp::BoolV(..)
//         | AstOp::BVS(..)
//         | AstOp::BVV(..)
//         | AstOp::FPS(..)
//         | AstOp::FPV(..)
//         | AstOp::StringS(..)
//         | AstOp::StringV(..) => ast.clone(),
//         AstOp::Not(ast) => {
//             simplify!(ast);
//             match &ast.op() {
//                 AstOp::Not(ast) => ast.clone(),
//                 AstOp::BoolV(v) => ctx.boolv(!v)?,
//                 AstOp::BVV(v) => ctx.bvv(!v.clone())?,
//                 _ => ctx.not(&ast)?,
//             }
//         }
//         AstOp::And(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BoolV(lhs), AstOp::BoolV(rhs)) => ctx.boolv(*lhs && *rhs)?,
//                 (AstOp::BoolV(true), v) | (v, AstOp::BoolV(true)) => ctx.make_ast(v.clone())?,
//                 (AstOp::BoolV(false), _) | (_, AstOp::BoolV(false)) => ctx.false_()?,
//                 (AstOp::Not(lhs), AstOp::Not(rhs)) => ctx.not(&ctx.or(lhs, rhs)?)?,
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() & rhs.clone())?,
//                 _ => ctx.and(&lhs, &rhs)?,
//             }
//         }
//         AstOp::Or(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BoolV(lhs), AstOp::BoolV(rhs)) => ctx.boolv(*lhs || *rhs)?,
//                 (AstOp::BoolV(true), _) | (_, AstOp::BoolV(true)) => ctx.true_()?,
//                 (AstOp::BoolV(false), v) | (v, AstOp::BoolV(false)) => ctx.make_ast(v.clone())?,
//                 (AstOp::Not(lhs), AstOp::Not(rhs)) => ctx.not(&ctx.and(lhs, rhs)?)?,
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() | rhs.clone())?,
//                 _ => ctx.or(&lhs, &rhs)?,
//             }
//         }
//         AstOp::Xor(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BoolV(lhs), AstOp::BoolV(rhs)) => ctx.boolv(*lhs ^ *rhs)?,
//                 (AstOp::BoolV(true), v) | (v, AstOp::BoolV(true)) => {
//                     ctx.not(&ctx.make_ast(v.clone())?)?
//                 }
//                 (AstOp::BoolV(false), v) | (v, AstOp::BoolV(false)) => ctx.make_ast(v.clone())?,
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() ^ rhs.clone())?,
//                 _ => ctx.xor(&lhs, &rhs)?,
//             }
//         }
//         AstOp::Add(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() + rhs.clone())?,
//                 _ => ctx.add(&lhs, &rhs)?,
//             }
//         }
//         AstOp::Sub(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() - rhs.clone())?,
//                 _ => ctx.sub(&lhs, &rhs)?,
//             }
//         }
//         AstOp::Mul(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() * rhs.clone())?,
//                 _ => ctx.mul(&lhs, &rhs)?,
//             }
//         }
//         AstOp::UDiv(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() / rhs.clone())?,
//                 _ => ctx.udiv(&lhs, &rhs)?,
//             }
//         }
//         AstOp::SDiv(_, _) => todo!(),
//         AstOp::URem(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.bvv(lhs.clone() % rhs.clone())?,
//                 _ => ctx.urem(&lhs, &rhs)?,
//             }
//         }
//         AstOp::SRem(_, _) => todo!(),
//         AstOp::Pow(_, _) => todo!(),
//         AstOp::LShL(_, _) => todo!(),
//         AstOp::LShR(_, _) => todo!(),
//         AstOp::AShL(_, _) => todo!(),
//         AstOp::AShR(_, _) => todo!(),
//         AstOp::RotateLeft(_, _) => todo!(),
//         AstOp::RotateRight(_, _) => todo!(),
//         AstOp::ZeroExt(_, _) => todo!(),
//         AstOp::SignExt(_, _) => todo!(),
//         AstOp::Extract(_, _, _) => todo!(),
//         AstOp::Concat(_, _) => todo!(),
//         AstOp::Reverse(ast) => {
//             simplify!(ast);
//             match &ast.op() {
//                 AstOp::BVV(v) => ctx.bvv(v.clone().reverse())?,
//                 AstOp::Reverse(ast) => ast.clone(),
//                 _ => ctx.reverse(&ast)?,
//             }
//         }
//         AstOp::Eq(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs == rhs)?,
//                 _ => ctx.eq_(&lhs, &rhs)?,
//             }
//         }
//         AstOp::Neq(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs != rhs)?,
//                 _ => ctx.neq(&lhs, &rhs)?,
//             }
//         }
//         AstOp::ULT(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs < rhs)?,
//                 _ => ctx.ult(&lhs, &rhs)?,
//             }
//         }
//         AstOp::ULE(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs <= rhs)?,
//                 _ => ctx.ule(&lhs, &rhs)?,
//             }
//         }
//         AstOp::UGT(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs > rhs)?,
//                 _ => ctx.ugt(&lhs, &rhs)?,
//             }
//         }
//         AstOp::UGE(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs >= rhs)?,
//                 _ => ctx.uge(&lhs, &rhs)?,
//             }
//         }
//         AstOp::SLT(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs < rhs)?,
//                 _ => ctx.slt(&lhs, &rhs)?,
//             }
//         }
//         AstOp::SLE(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs <= rhs)?,
//                 _ => ctx.sle(&lhs, &rhs)?,
//             }
//         }
//         AstOp::SGT(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs > rhs)?,
//                 _ => ctx.sgt(&lhs, &rhs)?,
//             }
//         }
//         AstOp::SGE(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::BVV(lhs), AstOp::BVV(rhs)) => ctx.boolv(lhs >= rhs)?,
//                 _ => ctx.sge(&lhs, &rhs)?,
//             }
//         }
//         AstOp::FpToFp(_, _, _) => todo!(),
//         AstOp::BvToFpUnsigned(_, _, _) => todo!(),
//         AstOp::FpToIEEEBV(_) => todo!(),
//         AstOp::FpToUBV(_, _, _) => todo!(),
//         AstOp::FpToSBV(_, _, _) => todo!(),
//         AstOp::FpNeg(_, _) => todo!(),
//         AstOp::FpAbs(_, _) => todo!(),
//         AstOp::FpAdd(_, _, _) => todo!(),
//         AstOp::FpSub(_, _, _) => todo!(),
//         AstOp::FpMul(_, _, _) => todo!(),
//         AstOp::FpDiv(_, _, _) => todo!(),
//         AstOp::FpSqrt(_, _) => todo!(),
//         AstOp::FpEq(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::FPV(lhs), AstOp::FPV(rhs)) => ctx.boolv(lhs == rhs)?,
//                 _ => ctx.fp_eq(&lhs, &rhs)?,
//             }
//         }
//         AstOp::FpNeq(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::FPV(lhs), AstOp::FPV(rhs)) => ctx.boolv(lhs != rhs)?,
//                 _ => ctx.fp_neq(&lhs, &rhs)?,
//             }
//         }
//         AstOp::FpLt(_, _) => todo!(),
//         AstOp::FpLeq(_, _) => todo!(),
//         AstOp::FpGt(_, _) => todo!(),
//         AstOp::FpGeq(_, _) => todo!(),
//         AstOp::FpIsNan(_) => todo!(),
//         AstOp::FpIsInf(_) => todo!(),
//         AstOp::StrLen(_) => todo!(),
//         AstOp::StrConcat(_, _) => todo!(),
//         AstOp::StrSubstr(_, _, _) => todo!(),
//         AstOp::StrContains(_, _) => todo!(),
//         AstOp::StrIndexOf(_, _, _) => todo!(),
//         AstOp::StrReplace(_, _, _) => todo!(),
//         AstOp::StrPrefixOf(_, _) => todo!(),
//         AstOp::StrSuffixOf(_, _) => todo!(),
//         AstOp::StrToBV(_) => todo!(),
//         AstOp::BVToStr(_) => todo!(),
//         AstOp::StrIsDigit(_) => todo!(),
//         AstOp::StrEq(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::StringV(lhs), AstOp::StringV(rhs)) => ctx.boolv(lhs == rhs)?,
//                 _ => ctx.streq(&lhs, &rhs)?,
//             }
//         }
//         AstOp::StrNeq(lhs, rhs) => {
//             simplify!(lhs, rhs);
//             match (lhs.op(), rhs.op()) {
//                 (AstOp::StringV(lhs), AstOp::StringV(rhs)) => ctx.boolv(lhs != rhs)?,
//                 _ => ctx.strneq(&lhs, &rhs)?,
//             }
//         }
//         AstOp::If(cond, then, else_) => {
//             simplify!(cond, then, else_);
//             match &cond.op() {
//                 AstOp::BoolV(true) => then.clone(),
//                 AstOp::BoolV(false) => else_.clone(),
//                 _ => ctx.if_(&cond, &then, &else_)?,
//             }
//         }
//         AstOp::Annotated(ast, anno) => {
//             simplify!(ast);
//             if anno.eliminatable() {
//                 ast.clone()
//             } else {
//                 ctx.annotated(&ast, anno.clone())?
//             }
//         }
//     };

//     ctx.simplification_cache
//         .write()?
//         .insert(ast.hash(), Arc::downgrade(&ast));
//     Ok(ast)
// }
