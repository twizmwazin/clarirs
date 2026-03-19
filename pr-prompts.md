# PR Prompts for Clarirs Maintainability Improvements

Paste each of these into a separate Claude Code session. Each is self-contained.

---

## PR #2: Systematic Hash Discriminants

```
In the clarirs repo, create a branch `fix/systematic-hash-discriminants` from `origin/main` and make this change:

The hand-written `Hash` impls for `BooleanOp`, `BitVecOp`, `FloatOp`, and `StringOp` use magic integer discriminants that are error-prone (e.g., BitVecOp skips discriminant 14). Replace them with `std::mem::discriminant(self)`.

For each Op enum's Hash impl in crates/clarirs_core/src/ast/{bool,bitvec,float,string}.rs, change from:

    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "bool".hash(state);
        match self {
            BooleanOp::BoolS(s) => { 0.hash(state); s.hash(state); }
            BooleanOp::BoolV(b) => { 1.hash(state); b.hash(state); }
            ...
        }
    }

To:

    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        "bool".hash(state);
        std::mem::discriminant(self).hash(state);
        match self {
            BooleanOp::BoolS(s) => { s.hash(state); }
            BooleanOp::BoolV(b) => { b.hash(state); }
            ...
        }
    }

Apply this to all four Op enums. The domain-separation string ("bool", "bv", "float", "string") is already present and prevents cross-type collisions. The discriminant() call provides automatic unique-per-variant hashing.

Run `cargo check -p clarirs_core` and `cargo test -p clarirs_core` to verify. Commit and push.
```

---

## PR #4: Replace .unwrap() on Lock Results

```
In the clarirs repo, create a branch `fix/replace-lock-unwraps` from `origin/main` and make this change:

Replace `.unwrap()` calls on RwLock `.read()` and `.write()` results in crates/clarirs_core/src/ with proper error handling. The codebase already has `ClarirsError::CacheLockPoisoned` and `From<PoisonError<T>>` impl in error.rs.

Rules:
- In functions returning `Result<_, ClarirsError>`: change `.unwrap()` to `?`
- In functions NOT returning Result (like `intern_string`): change `.unwrap()` to `.expect("descriptive message")`
- Only change lock-related unwraps (`.read().unwrap()`, `.write().unwrap()`), NOT Option unwraps or other kinds
- Focus on crates/clarirs_core/src/ only (cache.rs, context.rs, and any others)

Note: In cache.rs, `Cache::get_or_insert` has a generic error type `E`, so `?` won't work there directly. For those, use `.expect("cache lock poisoned")`.

Run `cargo check -p clarirs_core` and `cargo test -p clarirs_core` to verify. Commit and push.
```

---

## PR #5: Fix Error Type Design Issues

```
In the clarirs repo, create a branch `fix/error-type-cleanup` from `origin/main` and make these changes:

1. In crates/clarirs_core/src/error.rs:
   - Remove the `InvalidArguments` variant (the one with no message)
   - Rename `InvalidArgumentsWithMessage(String)` to `InvalidArguments(String)`
   - Fix typo on line 24: "bite-sized" → "byte-sized"
   - Fix empty string on line 63: change `ClarirsError::ConversionError("".to_string())` to `ClarirsError::ConversionError("BitVec conversion error".to_string())`

2. Search the ENTIRE workspace for `ClarirsError::InvalidArguments` (the no-message version, which will now be a compile error) and replace each with `ClarirsError::InvalidArguments("descriptive message".to_string())` using a context-appropriate message.

3. Search the ENTIRE workspace for `InvalidArgumentsWithMessage` and replace with `InvalidArguments`.

Run `cargo check` (whole workspace) to verify all crates compile. Commit and push.
```

---

## PR #6: Op::variables() Return Cow

```
In the clarirs repo, create a branch `fix/variables-return-cow` from `origin/main` and make this change:

Change `Op::variables()` to return `Cow<'_, BTreeSet<InternedString>>` instead of `BTreeSet<InternedString>` to avoid unnecessary cloning.

1. In crates/clarirs_core/src/ast/op.rs:
   - Add `use std::borrow::Cow;`
   - Change `fn variables(&self) -> BTreeSet<InternedString>;` to `fn variables(&self) -> Cow<'_, BTreeSet<InternedString>>;`

2. In crates/clarirs_core/src/ast/node.rs:
   - `impl Op for AstNode`: return `Cow::Borrowed(&self.variables)`
   - `impl Op for DynAst`: delegate to inner and return appropriately
   - Public `AstNode::variables()` method: change to return `&BTreeSet<InternedString>`

3. In crates/clarirs_core/src/ast/{bool,bitvec,float,string}.rs:
   - Each `Op::variables()` impl: wrap the return in `Cow::Owned(...)`

4. Fix all call sites across the ENTIRE workspace that now receive Cow instead of BTreeSet. They may need `.into_owned()`, `.as_ref()`, `&*`, or `.clone()`. Key places to check:
   - crates/clarirs_core/src/solver/ (variables method)
   - crates/clarirs_core/src/algorithms/
   - crates/clarirs_z3/
   - crates/clarirs-vsa/
   - crates/clarirs_py/

Run `cargo check` (whole workspace) to verify ALL crates compile. Commit and push.
```

---

## PR #7: Fix Child Iterator Index Type Inconsistency

```
In the clarirs repo, create a branch `fix/child-iter-index-type` from `origin/main` and make this change:

`BooleanOpChildIter` in crates/clarirs_core/src/ast/bool.rs uses `u8` for its `index` field, while `BitVecOpChildIter` uses `usize`. This artificially limits And/Or to 255 children and is inconsistent.

1. In crates/clarirs_core/src/ast/bool.rs:
   - Change `index: u8` to `index: usize` in `BooleanOpChildIter`
   - In the `next()` method, remove `as usize` casts on `i` (they're no longer needed)
   - In `ExactSizeIterator::len()`, remove `as usize` cast on `self.index`

2. Check crates/clarirs_core/src/ast/float.rs and string.rs for the same issue and fix if needed.

Run `cargo check -p clarirs_core` to verify. Commit and push.
```

---

## PR #8: Remove Unnecessary Clones in DynAst::From Impls

```
In the clarirs repo, create a branch `fix/remove-unnecessary-dynast-clones` from `origin/main` and make this change:

In crates/clarirs_core/src/ast/node.rs, the `From<BoolAst>`, `From<BitVecAst>`, `From<FloatAst>`, and `From<StringAst>` impls for DynAst (the OWNED versions, NOT the `From<&XAst>` versions) unnecessarily clone the Arc.

Change these four impls from:
    impl<'c> From<BoolAst<'c>> for DynAst<'c> {
        fn from(ast: BoolAst<'c>) -> Self {
            DynAst::Boolean(ast.clone())
        }
    }
To:
    impl<'c> From<BoolAst<'c>> for DynAst<'c> {
        fn from(ast: BoolAst<'c>) -> Self {
            DynAst::Boolean(ast)
        }
    }

Do NOT touch the `From<&BoolAst>` etc. impls - those need clone.

Run `cargo check -p clarirs_core` to verify. Commit and push.
```

---

## PR #11: Fix modular_arithmatic Typo

```
In the clarirs repo, create a branch `fix/arithmetic-typo` from `origin/main` and make this change:

The file crates/clarirs-vsa/src/strided_interval/modular_arithmatic.rs has "arithmatic" misspelled.

1. `git mv crates/clarirs-vsa/src/strided_interval/modular_arithmatic.rs crates/clarirs-vsa/src/strided_interval/modular_arithmetic.rs`
2. In crates/clarirs-vsa/src/strided_interval.rs, change:
   - `mod modular_arithmatic;` → `mod modular_arithmetic;`
   - `use modular_arithmatic::*;` → `use modular_arithmetic::*;`
3. Search for any other references to `modular_arithmatic` in the codebase and fix them.

Run `cargo check -p clarirs-vsa` to verify. Commit and push.
```

---

## PR #12: GenericCache Read-Then-Write Pattern

```
In the clarirs repo, create a branch `fix/generic-cache-read-then-write` from `origin/main` and make this change:

In crates/clarirs_core/src/cache.rs, `GenericCache::get_or_insert` (around line 40) immediately acquires a write lock even for cache hits. Change it to use a read-then-write pattern consistent with `AstCache`.

Change from:
    fn get_or_insert<E>(&self, key: K, mut value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E> {
        let mut locked = self.0.write().unwrap();
        match locked.get(&key) {
            Some(value) => Ok(value.clone()),
            None => {
                let value = value_cv()?;
                locked.insert(key, value.clone());
                Ok(value)
            }
        }
    }

To:
    fn get_or_insert<E>(&self, key: K, mut value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E> {
        // Fast path: check with read lock
        {
            let locked = self.0.read().unwrap();
            if let Some(value) = locked.get(&key) {
                return Ok(value.clone());
            }
        }
        // Slow path: compute and insert with write lock
        let mut locked = self.0.write().unwrap();
        // Double-check after acquiring write lock
        if let Some(value) = locked.get(&key) {
            return Ok(value.clone());
        }
        let value = value_cv()?;
        locked.insert(key, value.clone());
        Ok(value)
    }

Note: K needs to also implement Clone for the key to be usable across both lock scopes. Check if K: Clone is already a bound or needs to be added.

Run `cargo check -p clarirs_core` and `cargo test -p clarirs_core -- cache` to verify. Commit and push.
```
