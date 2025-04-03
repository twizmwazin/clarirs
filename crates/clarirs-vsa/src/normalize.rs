use clarirs_core::ast::annotation::AnnotationType;
use clarirs_core::ast::bitvec::BitVecOpExt;
use clarirs_core::prelude::*;

/// The `Normalize` trait provides functionality to convert AST nodes into a normalized form
/// suitable for Value Set Analysis (VSA).
///
/// This trait is implemented for both `BitVecAst` and `BoolAst` types, allowing for
/// normalization of both bitvector and boolean expressions. The normalization process
/// converts symbolic values (BVS) and concrete values (BVV) into Strided Interval (SI)
/// representation, which is the core abstraction used in VSA.
///
/// # Error Handling
///
/// The normalization process will return errors for:
/// - BVS nodes without SI annotations
/// - Floating point operations (not supported in VSA)
/// - String operations (not supported in VSA)
///
/// # Examples
///
/// ```
/// use clarirs_core::prelude::*;
/// use clarirs_vsa::normalize::Normalize;
///
/// fn example<'c>(ctx: &'c Context<'c>) -> Result<(), ClarirsError> {
///     // Create a bitvector value
///     let bv = ctx.bvv_prim(42u32)?;
///
///     // Normalize it for VSA
///     let normalized = bv.normalize()?;
///
///     // The result will be an SI representation
///     Ok(())
/// }
/// ```
pub trait Normalize<'c>: Sized {
    /// Normalizes an AST node for Value Set Analysis.
    ///
    /// This function converts the AST node into a form suitable for VSA by:
    /// - Converting BVV (concrete bitvector values) to SI (Strided Interval) form
    /// - Processing annotations, particularly SI annotations
    /// - Recursively normalizing child nodes for compound expressions
    /// - Rejecting unsupported operations (floating point, string operations)
    ///
    /// # Returns
    ///
    /// - `Ok(Self)` - A normalized version of the AST node
    /// - `Err(ClarirsError)` - If normalization fails due to unsupported operations
    ///   or invalid node types
    ///
    /// # Errors
    ///
    /// Will return `ClarirsError::UnsupportedOperation` if:
    /// - A BVS node doesn't have an SI annotation
    /// - The AST contains floating point operations
    /// - The AST contains string operations
    fn normalize(&self) -> Result<Self, ClarirsError>;
}

/// Implementation of the `Normalize` trait for bitvector AST nodes.
///
/// This implementation handles the normalization of bitvector expressions by:
/// 1. Converting BVV nodes to SI representation
/// 2. Rejecting BVS nodes without SI annotations
/// 3. Recursively normalizing child nodes for compound operations
/// 4. Rejecting floating point and string operations
/// 5. Preserving SI annotations
impl Normalize<'_> for BitVecAst<'_> {
    fn normalize(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();

        match self.op() {
            BitVecOp::BVS(_, _) => Err(ClarirsError::UnsupportedOperation(
                "VSA expects BVS to have an SI annotation".to_string(),
            )),
            BitVecOp::BVV(bv) => ctx.si(
                bv.len(),
                1u32.into(),
                bv.to_biguint(),
                bv.to_biguint(),
            ),
            BitVecOp::Not(ast) => ctx.not(&ast.normalize()?),
            BitVecOp::And(lhs, rhs) => ctx.and(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Or(lhs, rhs) => ctx.or(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Xor(lhs, rhs) => ctx.xor(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Neg(ast) => ctx.neg(&ast.normalize()?),
            BitVecOp::Add(lhs, rhs) => ctx.add(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Sub(lhs, rhs) => ctx.sub(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Mul(lhs, rhs) => ctx.mul(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::UDiv(lhs, rhs) => ctx.udiv(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::SDiv(lhs, rhs) => ctx.sdiv(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::URem(lhs, rhs) => ctx.urem(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::SRem(lhs, rhs) => ctx.srem(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::ShL(lhs, rhs) => ctx.shl(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::LShR(lhs, rhs) => ctx.lshr(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::AShR(lhs, rhs) => ctx.ashr(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::RotateLeft(lhs, rhs) => ctx.rotate_left(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::RotateRight(lhs, rhs) => {
                ctx.rotate_right(&lhs.normalize()?, &rhs.normalize()?)
            }
            BitVecOp::ZeroExt(ast, size) => ctx.zero_ext(&ast.normalize()?, *size),
            BitVecOp::SignExt(ast, size) => ctx.sign_ext(&ast.normalize()?, *size),
            BitVecOp::Extract(ast, high, low) => ctx.extract(&ast.normalize()?, *high, *low),
            BitVecOp::Concat(lhs, rhs) => ctx.concat(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Reverse(ast) => ctx.reverse(&ast.normalize()?),
            BitVecOp::FpToIEEEBV(_) | BitVecOp::FpToUBV(_, _, _) | BitVecOp::FpToSBV(_, _, _) => {
                Err(ClarirsError::UnsupportedOperation(
                    "Floating point operations are not supported in VSA".to_string(),
                ))
            }
            BitVecOp::StrLen(_) | BitVecOp::StrIndexOf(_, _, _) | BitVecOp::StrToBV(_) => {
                Err(ClarirsError::UnsupportedOperation(
                    "String operations are not supported in VSA".to_string(),
                ))
            }
            BitVecOp::If(cond, then_branch, else_branch) => ctx.if_(
                &cond.normalize()?,
                &then_branch.normalize()?,
                &else_branch.normalize()?,
            ),
            BitVecOp::Annotated(ast, annotation) => match annotation.type_() {
                AnnotationType::StridedInterval {
                    stride,
                    lower_bound,
                    upper_bound,
                } => ctx.si(
                    ast.size(),
                    stride.clone(),
                    lower_bound.clone(),
                    upper_bound.clone(),
                ),
                _ => ctx.annotated(&ast.normalize()?, annotation.clone()),
            },
            BitVecOp::SI(..) => Ok(self.clone()),
            BitVecOp::Union(lhs, rhs) => ctx.union(&lhs.normalize()?, &rhs.normalize()?),
            BitVecOp::Intersection(lhs, rhs) => {
                ctx.intersection(&lhs.normalize()?, &rhs.normalize()?)
            }
        }
    }
}

/// Implementation of the `Normalize` trait for boolean AST nodes.
///
/// This implementation handles the normalization of boolean expressions by:
/// 1. Preserving BoolS and BoolV nodes as they are
/// 2. Recursively normalizing child nodes for compound operations
/// 3. Rejecting floating point and string operations
/// 4. Preserving annotations
impl Normalize<'_> for BoolAst<'_> {
    fn normalize(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();

        match self.op() {
            // BoolS is "Top", BoolV is True/False. Bottom is unsat
            BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(self.clone()),
            BooleanOp::Not(ast) => ctx.not(&ast.normalize()?),
            BooleanOp::And(lhs, rhs) => ctx.and(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::Or(lhs, rhs) => ctx.or(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::Xor(lhs, rhs) => ctx.xor(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::BoolEq(lhs, rhs) => ctx.eq_(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::BoolNeq(lhs, rhs) => ctx.neq(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::Eq(lhs, rhs) => ctx.eq_(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::Neq(lhs, rhs) => ctx.neq(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::ULT(lhs, rhs) => ctx.ult(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::ULE(lhs, rhs) => ctx.ule(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::UGT(lhs, rhs) => ctx.ugt(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::UGE(lhs, rhs) => ctx.uge(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::SLT(lhs, rhs) => ctx.slt(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::SLE(lhs, rhs) => ctx.sle(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::SGT(lhs, rhs) => ctx.sgt(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::SGE(lhs, rhs) => ctx.sge(&lhs.normalize()?, &rhs.normalize()?),
            BooleanOp::FpEq(..)
            | BooleanOp::FpNeq(..)
            | BooleanOp::FpLt(..)
            | BooleanOp::FpLeq(..)
            | BooleanOp::FpGt(..)
            | BooleanOp::FpGeq(..)
            | BooleanOp::FpIsNan(..)
            | BooleanOp::FpIsInf(..) => Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported in VSA".to_string(),
            )),
            BooleanOp::StrContains(..)
            | BooleanOp::StrPrefixOf(..)
            | BooleanOp::StrSuffixOf(..)
            | BooleanOp::StrIsDigit(..)
            | BooleanOp::StrEq(..)
            | BooleanOp::StrNeq(..) => Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported in VSA".to_string(),
            )),
            BooleanOp::If(cond, then_branch, else_branch) => ctx.if_(
                &cond.normalize()?,
                &then_branch.normalize()?,
                &else_branch.normalize()?,
            ),
            BooleanOp::Annotated(ast, annotation) => {
                // For boolean ASTs, we just normalize the inner AST
                // as there's no SI equivalent for boolean operations
                ctx.annotated(&ast.normalize()?, annotation.clone())
            }
        }
    }
}

impl Normalize<'_> for DynAst<'_> {
    fn normalize(&self) -> Result<Self, ClarirsError> {
        match self {
            DynAst::BitVec(ast) => ast.normalize().map(DynAst::BitVec),
            DynAst::Boolean(ast) => ast.normalize().map(DynAst::Boolean),
            DynAst::Float(_) => Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported in VSA".to_string(),
            )),
            DynAst::String(_) => Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported in VSA".to_string(),
            )),
        }
    }
}
