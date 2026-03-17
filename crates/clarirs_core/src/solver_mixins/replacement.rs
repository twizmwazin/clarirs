use std::collections::HashMap;

use crate::algorithms::{
    post_order::{bitvec_child, bool_child, float_child, string_child},
    walk_post_order,
};
use crate::prelude::*;

/// A solver mixin that applies expression replacements before delegating to the
/// inner solver. This is a Rust port of claripy's `ReplacementFrontend`.
///
/// Replacements map symbolic (sub-)expressions to simpler or concrete values.
/// When constraints of the form `x == val` (where one side is symbolic and the
/// other concrete) are added, the mixin can automatically record a replacement.
/// All solver queries then transparently substitute known replacements before
/// reaching the underlying solver, which can dramatically speed up solving.
#[derive(Clone, Debug)]
pub struct ReplacementMixin<'c, S: Solver<'c>> {
    inner: S,
    /// Canonical replacement map: AST hash → replacement DynAst.
    replacements: HashMap<u64, DynAst<'c>>,
    /// Expanded cache (includes transitive replacements).
    replacement_cache: HashMap<u64, DynAst<'c>>,
    /// Whether to automatically extract replacements from added constraints.
    auto_replace: bool,
    /// Whether to record solve results as replacements (less safe but faster).
    unsafe_replacement: bool,
    _marker: std::marker::PhantomData<&'c ()>,
}

impl<'c, S: Solver<'c>> ReplacementMixin<'c, S> {
    pub fn new(inner: S) -> Self {
        Self {
            inner,
            replacements: HashMap::new(),
            replacement_cache: HashMap::new(),
            auto_replace: true,
            unsafe_replacement: false,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn new_with_options(inner: S, auto_replace: bool, unsafe_replacement: bool) -> Self {
        Self {
            inner,
            replacements: HashMap::new(),
            replacement_cache: HashMap::new(),
            auto_replace,
            unsafe_replacement,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut S {
        &mut self.inner
    }

    // ------------------------------------------------------------------
    // Replacement management
    // ------------------------------------------------------------------

    /// Register a replacement: future occurrences of `old` will be replaced
    /// with `new` before reaching the inner solver.
    pub fn add_replacement(&mut self, old: DynAst<'c>, new: DynAst<'c>) {
        let hash = old.inner_hash();
        self.replacements.insert(hash, new.clone());
        // Invalidate the transitive cache – rebuild from scratch.
        self.replacement_cache = self.replacements.clone();
    }

    /// Remove specific replacements by their original-expression hashes.
    pub fn remove_replacements(&mut self, hashes: &[u64]) {
        for h in hashes {
            self.replacements.remove(h);
        }
        self.replacement_cache = self.replacements.clone();
    }

    /// Drop all recorded replacements.
    pub fn clear_replacements(&mut self) {
        self.replacements.clear();
        self.replacement_cache.clear();
    }

    /// Return a read-only view of the current replacements.
    pub fn replacements(&self) -> &HashMap<u64, DynAst<'c>> {
        &self.replacements
    }

    // ------------------------------------------------------------------
    // Internal helpers
    // ------------------------------------------------------------------

    /// Apply all known replacements to a boolean AST.
    fn replace_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_bool()
                .ok_or_else(|| ClarirsError::TypeError("Expected BoolAst in cache".to_string()));
        }
        let dyn_ast = DynAst::Boolean(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_bool().ok_or_else(|| {
            ClarirsError::TypeError("Expected BoolAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::Boolean(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to a bitvec AST.
    fn replace_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_bitvec()
                .ok_or_else(|| ClarirsError::TypeError("Expected BitVecAst in cache".to_string()));
        }
        let dyn_ast = DynAst::BitVec(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_bitvec().ok_or_else(|| {
            ClarirsError::TypeError("Expected BitVecAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::BitVec(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to a float AST.
    fn replace_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_float()
                .ok_or_else(|| ClarirsError::TypeError("Expected FloatAst in cache".to_string()));
        }
        let dyn_ast = DynAst::Float(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_float().ok_or_else(|| {
            ClarirsError::TypeError("Expected FloatAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::Float(result.clone()));
        Ok(result)
    }

    /// Apply all known replacements to a string AST.
    fn replace_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        if self.replacement_cache.is_empty() || !expr.symbolic() {
            return Ok(expr.clone());
        }
        let hash = expr.hash();
        if let Some(cached) = self.replacement_cache.get(&hash) {
            return cached
                .clone()
                .into_string()
                .ok_or_else(|| ClarirsError::TypeError("Expected StringAst in cache".to_string()));
        }
        let dyn_ast = DynAst::String(expr.clone());
        let replaced = self.apply_replacements(dyn_ast)?;
        let result = replaced.into_string().ok_or_else(|| {
            ClarirsError::TypeError("Expected StringAst after replacement".to_string())
        })?;
        self.replacement_cache
            .insert(hash, DynAst::String(result.clone()));
        Ok(result)
    }

    /// Walk the AST in post-order, replacing any sub-expression whose hash
    /// appears in the replacement cache. This is a single-pass O(n) traversal.
    fn apply_replacements(&self, ast: DynAst<'c>) -> Result<DynAst<'c>, ClarirsError> {
        let cache = &self.replacement_cache;
        let ctx = ast.context();

        walk_post_order(
            ast,
            |node, children| {
                // If this node has a replacement, use it directly.
                if let Some(replacement) = cache.get(&node.inner_hash()) {
                    return Ok(replacement.clone());
                }

                // If this is a leaf or has no children that changed, return as-is.
                if children.is_empty() {
                    return Ok(node);
                }

                // Rebuild the node with (possibly replaced) children.
                match &node {
                    DynAst::Boolean(bool_ast) => match bool_ast.op() {
                        BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(bool_ast.clone()),
                        BooleanOp::Not(..) => ctx.not(bool_child(children, 0)?),
                        BooleanOp::And(..) => {
                            let args: Vec<_> = children
                                .iter()
                                .map(|c| bool_child(std::slice::from_ref(c), 0))
                                .collect::<Result<_, _>>()?;
                            ctx.and(args)
                        }
                        BooleanOp::Or(..) => {
                            let args: Vec<_> = children
                                .iter()
                                .map(|c| bool_child(std::slice::from_ref(c), 0))
                                .collect::<Result<_, _>>()?;
                            ctx.or(args)
                        }
                        BooleanOp::Xor(..) => {
                            ctx.xor(bool_child(children, 0)?, bool_child(children, 1)?)
                        }
                        BooleanOp::BoolEq(..) => {
                            ctx.eq_(bool_child(children, 0)?, bool_child(children, 1)?)
                        }
                        BooleanOp::BoolNeq(..) => {
                            ctx.neq(bool_child(children, 0)?, bool_child(children, 1)?)
                        }
                        BooleanOp::Eq(..) => {
                            ctx.eq_(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::Neq(..) => {
                            ctx.neq(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::ULT(..) => {
                            ctx.ult(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::ULE(..) => {
                            ctx.ule(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::UGT(..) => {
                            ctx.ugt(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::UGE(..) => {
                            ctx.uge(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::SLT(..) => {
                            ctx.slt(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::SLE(..) => {
                            ctx.sle(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::SGT(..) => {
                            ctx.sgt(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::SGE(..) => {
                            ctx.sge(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BooleanOp::FpEq(..) => {
                            ctx.fp_eq(float_child(children, 0)?, float_child(children, 1)?)
                        }
                        BooleanOp::FpNeq(..) => {
                            ctx.fp_neq(float_child(children, 0)?, float_child(children, 1)?)
                        }
                        BooleanOp::FpLt(..) => {
                            ctx.fp_lt(float_child(children, 0)?, float_child(children, 1)?)
                        }
                        BooleanOp::FpLeq(..) => {
                            ctx.fp_leq(float_child(children, 0)?, float_child(children, 1)?)
                        }
                        BooleanOp::FpGt(..) => {
                            ctx.fp_gt(float_child(children, 0)?, float_child(children, 1)?)
                        }
                        BooleanOp::FpGeq(..) => {
                            ctx.fp_geq(float_child(children, 0)?, float_child(children, 1)?)
                        }
                        BooleanOp::FpIsNan(..) => ctx.fp_is_nan(float_child(children, 0)?),
                        BooleanOp::FpIsInf(..) => ctx.fp_is_inf(float_child(children, 0)?),
                        BooleanOp::StrContains(..) => {
                            ctx.str_contains(string_child(children, 0)?, string_child(children, 1)?)
                        }
                        BooleanOp::StrPrefixOf(..) => ctx
                            .str_prefix_of(string_child(children, 0)?, string_child(children, 1)?),
                        BooleanOp::StrSuffixOf(..) => ctx
                            .str_suffix_of(string_child(children, 0)?, string_child(children, 1)?),
                        BooleanOp::StrIsDigit(..) => ctx.str_is_digit(string_child(children, 0)?),
                        BooleanOp::StrEq(..) => {
                            ctx.str_eq(string_child(children, 0)?, string_child(children, 1)?)
                        }
                        BooleanOp::StrNeq(..) => {
                            ctx.str_neq(string_child(children, 0)?, string_child(children, 1)?)
                        }
                        BooleanOp::ITE(..) => ctx.ite(
                            bool_child(children, 0)?,
                            bool_child(children, 1)?,
                            bool_child(children, 2)?,
                        ),
                    }
                    .map(DynAst::Boolean),
                    DynAst::BitVec(bv_ast) => match bv_ast.op() {
                        BitVecOp::BVS(..) | BitVecOp::BVV(..) => Ok(bv_ast.clone()),
                        BitVecOp::Not(..) => ctx.not(bitvec_child(children, 0)?),
                        BitVecOp::And(args) => {
                            let new_args: Vec<_> = (0..args.len())
                                .map(|i| bitvec_child(children, i))
                                .collect::<Result<_, _>>()?;
                            ctx.bv_and_many(new_args)
                        }
                        BitVecOp::Or(args) => {
                            let new_args: Vec<_> = (0..args.len())
                                .map(|i| bitvec_child(children, i))
                                .collect::<Result<_, _>>()?;
                            ctx.bv_or_many(new_args)
                        }
                        BitVecOp::Xor(args) => {
                            let new_args: Vec<_> = (0..args.len())
                                .map(|i| bitvec_child(children, i))
                                .collect::<Result<_, _>>()?;
                            ctx.bv_xor_many(new_args)
                        }
                        BitVecOp::Neg(..) => ctx.neg(bitvec_child(children, 0)?),
                        BitVecOp::Add(args) => {
                            let new_args: Vec<_> = (0..args.len())
                                .map(|i| bitvec_child(children, i))
                                .collect::<Result<_, _>>()?;
                            ctx.add_many(new_args)
                        }
                        BitVecOp::Sub(..) => {
                            ctx.sub(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::Mul(args) => {
                            let new_args: Vec<_> = (0..args.len())
                                .map(|i| bitvec_child(children, i))
                                .collect::<Result<_, _>>()?;
                            ctx.mul_many(new_args)
                        }
                        BitVecOp::UDiv(..) => {
                            ctx.udiv(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::SDiv(..) => {
                            ctx.sdiv(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::URem(..) => {
                            ctx.urem(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::SRem(..) => {
                            ctx.srem(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::ShL(..) => {
                            ctx.shl(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::LShR(..) => {
                            ctx.lshr(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::AShR(..) => {
                            ctx.ashr(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::RotateLeft(..) => {
                            ctx.rotate_left(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::RotateRight(..) => {
                            ctx.rotate_right(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::ZeroExt(_, size) => {
                            ctx.zero_ext(bitvec_child(children, 0)?, *size)
                        }
                        BitVecOp::SignExt(_, size) => {
                            ctx.sign_ext(bitvec_child(children, 0)?, *size)
                        }
                        BitVecOp::Extract(_, hi, lo) => {
                            ctx.extract(bitvec_child(children, 0)?, *hi, *lo)
                        }
                        BitVecOp::Concat(args) => {
                            let new_args: Vec<_> = (0..args.len())
                                .map(|i| bitvec_child(children, i))
                                .collect::<Result<_, _>>()?;
                            ctx.concat(new_args)
                        }
                        BitVecOp::ByteReverse(..) => ctx.byte_reverse(bitvec_child(children, 0)?),
                        BitVecOp::FpToIEEEBV(..) => ctx.fp_to_ieeebv(float_child(children, 0)?),
                        BitVecOp::FpToUBV(_, size, fprm) => {
                            ctx.fp_to_ubv(float_child(children, 0)?, *size, *fprm)
                        }
                        BitVecOp::FpToSBV(_, size, fprm) => {
                            ctx.fp_to_sbv(float_child(children, 0)?, *size, *fprm)
                        }
                        BitVecOp::StrLen(..) => ctx.str_len(string_child(children, 0)?),
                        BitVecOp::StrIndexOf(..) => ctx.str_index_of(
                            string_child(children, 0)?,
                            string_child(children, 1)?,
                            bitvec_child(children, 2)?,
                        ),
                        BitVecOp::StrToBV(..) => ctx.str_to_bv(string_child(children, 0)?),
                        BitVecOp::ITE(..) => ctx.ite(
                            bool_child(children, 0)?,
                            bitvec_child(children, 1)?,
                            bitvec_child(children, 2)?,
                        ),
                        BitVecOp::Union(..) => {
                            ctx.union(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::Intersection(..) => {
                            ctx.intersection(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                        BitVecOp::Widen(..) => {
                            ctx.widen(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                        }
                    }
                    .map(DynAst::BitVec),
                    DynAst::Float(float_ast) => match float_ast.op() {
                        FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(float_ast.clone()),
                        FloatOp::FpNeg(..) => ctx.fp_neg(float_child(children, 0)?),
                        FloatOp::FpAbs(..) => ctx.fp_abs(float_child(children, 0)?),
                        FloatOp::FpAdd(_, _, fprm) => {
                            ctx.fp_add(float_child(children, 0)?, float_child(children, 1)?, *fprm)
                        }
                        FloatOp::FpSub(_, _, fprm) => {
                            ctx.fp_sub(float_child(children, 0)?, float_child(children, 1)?, *fprm)
                        }
                        FloatOp::FpMul(_, _, fprm) => {
                            ctx.fp_mul(float_child(children, 0)?, float_child(children, 1)?, *fprm)
                        }
                        FloatOp::FpDiv(_, _, fprm) => {
                            ctx.fp_div(float_child(children, 0)?, float_child(children, 1)?, *fprm)
                        }
                        FloatOp::FpSqrt(_, fprm) => ctx.fp_sqrt(float_child(children, 0)?, *fprm),
                        FloatOp::FpToFp(_, fsort, fprm) => {
                            ctx.fp_to_fp(float_child(children, 0)?, *fsort, *fprm)
                        }
                        FloatOp::FpFP(..) => ctx.fp_fp(
                            bitvec_child(children, 0)?,
                            bitvec_child(children, 1)?,
                            bitvec_child(children, 2)?,
                        ),
                        FloatOp::BvToFp(_, fsort) => {
                            ctx.bv_to_fp(bitvec_child(children, 0)?, *fsort)
                        }
                        FloatOp::BvToFpSigned(_, fsort, fprm) => {
                            ctx.bv_to_fp_signed(bitvec_child(children, 0)?, *fsort, *fprm)
                        }
                        FloatOp::BvToFpUnsigned(_, fsort, fprm) => {
                            ctx.bv_to_fp_unsigned(bitvec_child(children, 0)?, *fsort, *fprm)
                        }
                        FloatOp::ITE(..) => ctx.ite(
                            bool_child(children, 0)?,
                            float_child(children, 1)?,
                            float_child(children, 2)?,
                        ),
                    }
                    .map(DynAst::Float),
                    DynAst::String(string_ast) => match string_ast.op() {
                        StringOp::StringS(..) | StringOp::StringV(..) => Ok(string_ast.clone()),
                        StringOp::StrConcat(..) => {
                            ctx.str_concat(string_child(children, 0)?, string_child(children, 1)?)
                        }
                        StringOp::StrSubstr(..) => ctx.str_substr(
                            string_child(children, 0)?,
                            bitvec_child(children, 1)?,
                            bitvec_child(children, 2)?,
                        ),
                        StringOp::StrReplace(..) => ctx.str_replace(
                            string_child(children, 0)?,
                            string_child(children, 1)?,
                            string_child(children, 2)?,
                        ),
                        StringOp::BVToStr(..) => ctx.bv_to_str(bitvec_child(children, 0)?),
                        StringOp::ITE(..) => ctx.ite(
                            bool_child(children, 0)?,
                            string_child(children, 1)?,
                            string_child(children, 2)?,
                        ),
                    }
                    .map(DynAst::String),
                }
            },
            &(),
        )
    }

    /// Try to extract a replacement from a constraint of the form `x == val`
    /// where one side is symbolic and the other is concrete, or `Not(x)` which
    /// implies `x == false`.
    fn extract_replacement(&mut self, constraint: &BoolAst<'c>) {
        if !constraint.symbolic() {
            return;
        }

        match constraint.op() {
            // Not(x) → replace x with false
            BooleanOp::Not(inner) => {
                if inner.symbolic() {
                    let ctx = constraint.context();
                    if let Ok(false_val) = ctx.false_() {
                        self.add_replacement(
                            DynAst::Boolean(inner.clone()),
                            DynAst::Boolean(false_val),
                        );
                    }
                }
            }
            // bool_a == bool_b where one is symbolic and one is concrete
            BooleanOp::BoolEq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::Boolean(old), DynAst::Boolean(new));
                }
            }
            // bv_a == bv_b where one is symbolic and one is concrete
            BooleanOp::Eq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::BitVec(old), DynAst::BitVec(new));
                }
            }
            // fp_a == fp_b where one is symbolic and one is concrete
            BooleanOp::FpEq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::Float(old), DynAst::Float(new));
                }
            }
            // str_a == str_b where one is symbolic and one is concrete
            BooleanOp::StrEq(a, b) => {
                if a.symbolic() ^ b.symbolic() {
                    let (old, new) = if a.symbolic() {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    self.add_replacement(DynAst::String(old), DynAst::String(new));
                }
            }
            _ => {}
        }
    }
}

impl<'c, S: Solver<'c>> HasContext<'c> for ReplacementMixin<'c, S> {
    fn context(&self) -> &'c Context<'c> {
        self.inner.context()
    }
}

impl<'c, S: Solver<'c>> Solver<'c> for ReplacementMixin<'c, S> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        // Extract replacements from simple equality constraints before adding.
        if self.auto_replace {
            self.extract_replacement(constraint);
        }

        // Apply existing replacements to the constraint before passing to inner.
        let replaced = self.replace_bool(constraint)?;
        self.inner.add(&replaced)
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        self.inner.clear()
    }

    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        self.inner.constraints()
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        self.inner.simplify()
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        self.inner.satisfiable()
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.is_true(&replaced)
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.is_false(&replaced)
    }

    fn has_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.has_true(&replaced)
    }

    fn has_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        self.inner.has_false(&replaced)
    }

    fn min_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.min_unsigned(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn max_unsigned(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.max_unsigned(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn min_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.min_signed(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn max_signed(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let result = self.inner.max_signed(&replaced)?;
        if self.unsafe_replacement && expr.symbolic() && !replaced.symbolic() {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(result.clone()));
        }
        Ok(result)
    }

    fn eval_bool_n(
        &mut self,
        expr: &BoolAst<'c>,
        n: u32,
    ) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        let replaced = self.replace_bool(expr)?;
        let results = self.inner.eval_bool_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(
                DynAst::Boolean(expr.clone()),
                DynAst::Boolean(first.clone()),
            );
        }
        Ok(results)
    }

    fn eval_bitvec_n(
        &mut self,
        expr: &BitVecAst<'c>,
        n: u32,
    ) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
        let replaced = self.replace_bitvec(expr)?;
        let results = self.inner.eval_bitvec_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(DynAst::BitVec(expr.clone()), DynAst::BitVec(first.clone()));
        }
        Ok(results)
    }

    fn eval_float_n(
        &mut self,
        expr: &FloatAst<'c>,
        n: u32,
    ) -> Result<Vec<FloatAst<'c>>, ClarirsError> {
        let replaced = self.replace_float(expr)?;
        let results = self.inner.eval_float_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(DynAst::Float(expr.clone()), DynAst::Float(first.clone()));
        }
        Ok(results)
    }

    fn eval_string_n(
        &mut self,
        expr: &StringAst<'c>,
        n: u32,
    ) -> Result<Vec<StringAst<'c>>, ClarirsError> {
        let replaced = self.replace_string(expr)?;
        let results = self.inner.eval_string_n(&replaced, n)?;
        if self.unsafe_replacement
            && expr.symbolic()
            && !replaced.symbolic()
            && let Some(first) = results.first()
        {
            self.add_replacement(DynAst::String(expr.clone()), DynAst::String(first.clone()));
        }
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_replacement_mixin_basic_bitvec_replacement() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create a symbolic variable and a concrete value
        let x = ctx.bvs("x", 8).unwrap();
        let five = ctx.bvv_prim(5u8).unwrap();

        // Manually add a replacement: x → 5
        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));

        // Evaluating x should now return 5 (after replacement makes it concrete)
        let result = solver.eval_bitvec(&x).unwrap();
        assert!(result.concrete());
        assert_eq!(result, five);
    }

    #[test]
    fn test_replacement_mixin_auto_replace_from_eq_constraint() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create x == 42
        let x = ctx.bvs("x", 64).unwrap();
        let forty_two = ctx.bvv_prim(42u64).unwrap();
        let constraint = ctx.eq_(&x, &forty_two).unwrap();

        // Adding this constraint should auto-extract x → 42
        solver.add(&constraint).unwrap();

        // Now evaluating x should return 42
        let result = solver.eval_bitvec(&x).unwrap();
        assert!(result.concrete());
        assert_eq!(result, forty_two);
    }

    #[test]
    fn test_replacement_mixin_auto_replace_from_not_constraint() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create Not(b) where b is symbolic
        let b = ctx.bools("b").unwrap();
        let not_b = ctx.not(&b).unwrap();

        // Adding Not(b) should auto-extract b → false
        solver.add(&not_b).unwrap();

        // Now evaluating b should return false
        let result = solver.eval_bool(&b).unwrap();
        assert!(result.concrete());
        assert!(result.is_false());
    }

    #[test]
    fn test_replacement_mixin_clear_replacements() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        let x = ctx.bvs("x", 8).unwrap();
        let five = ctx.bvv_prim(5u8).unwrap();

        solver.add_replacement(DynAst::BitVec(x.clone()), DynAst::BitVec(five.clone()));
        assert!(!solver.replacements().is_empty());

        solver.clear_replacements();
        assert!(solver.replacements().is_empty());
    }

    #[test]
    fn test_replacement_mixin_no_replace_concrete() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Concrete expressions should pass through without replacement
        let five = ctx.bvv_prim(5u8).unwrap();
        let result = solver.eval_bitvec(&five).unwrap();
        assert_eq!(result, five);
    }

    #[test]
    fn test_replacement_mixin_bool_eq_auto_replace() {
        let ctx = Context::new();
        let base_solver = ConcreteSolver::new(&ctx);
        let mut solver = ReplacementMixin::new(base_solver);

        // Create b == true where b is symbolic
        let b = ctx.bools("b").unwrap();
        let true_val = ctx.true_().unwrap();
        let constraint = ctx.eq_(&b, &true_val).unwrap();

        solver.add(&constraint).unwrap();

        let result = solver.eval_bool(&b).unwrap();
        assert!(result.is_true());
    }
}
