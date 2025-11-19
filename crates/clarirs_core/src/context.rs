use ahash::AHasher;
use std::{
    collections::{BTreeSet, HashMap},
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::{Arc, RwLock},
};

use crate::{
    cache::{AstCache, Cache},
    prelude::*,
};

/// An interned string that can be cloned cheaply and compared by pointer equality.
/// This is backed by an Arc<str> so cloning only increments a reference count.
#[derive(Clone, Debug, Eq)]
pub struct InternedString(Arc<str>);

impl InternedString {
    /// Get the string contents
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for InternedString {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl std::borrow::Borrow<str> for InternedString {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl PartialEq for InternedString {
    fn eq(&self, other: &Self) -> bool {
        // Fast pointer comparison first
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Hash for InternedString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the pointer, not the contents, for fast hashing
        Arc::as_ptr(&self.0).hash(state);
    }
}

impl std::fmt::Display for InternedString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl serde::Serialize for InternedString {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl Ord for InternedString {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for InternedString {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Default)]
#[allow(dead_code)] // FIXME: reintroduce simplification cache
pub struct Context<'c> {
    pub(crate) ast_cache: AstCache<'c>,
    pub(crate) simplification_cache: AstCache<'c>,
    pub(crate) excavate_ite_cache: AstCache<'c>,
    string_interner: RwLock<HashMap<Arc<str>, Arc<str>>>,
}

impl PartialEq for Context<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for Context<'_> {}

unsafe impl Send for Context<'_> {}
unsafe impl Sync for Context<'_> {}

impl Context<'_> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a string for use as a variable name.
    /// This ensures that identical strings share the same allocation and can be compared by pointer.
    pub fn intern_string(&self, s: impl AsRef<str>) -> InternedString {
        let s = s.as_ref();

        // Fast path: check if already interned with read lock
        {
            let interner = self.string_interner.read().unwrap();
            if let Some(existing) = interner.get(s) {
                return InternedString(Arc::clone(existing));
            }
        }

        // Slow path: intern the string with write lock
        let mut interner = self.string_interner.write().unwrap();
        // Double-check after acquiring write lock (another thread might have inserted it)
        if let Some(existing) = interner.get(s) {
            return InternedString(Arc::clone(existing));
        }

        let arc: Arc<str> = Arc::from(s);
        interner.insert(Arc::clone(&arc), Arc::clone(&arc));
        InternedString(arc)
    }
}

impl<'c> AstFactory<'c> for Context<'c> {
    fn intern_string(&self, s: impl AsRef<str>) -> InternedString {
        self.intern_string(s)
    }

    fn make_bool_annotated(
        &'c self,
        op: BooleanOp<'c>,
        mut annotations: BTreeSet<Annotation>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        0u32.hash(&mut hasher); // Domain separation for bools
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_bool()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))?
            .clone())
    }

    fn make_bitvec_annotated(
        &'c self,
        op: BitVecOp<'c>,
        mut annotations: BTreeSet<Annotation>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        1u32.hash(&mut hasher); // Domain separation for bitvecs
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_bitvec()
            .ok_or(ClarirsError::TypeError("Expected BitVecAst".to_string()))?
            .clone())
    }

    fn make_float_annotated(
        &'c self,
        op: FloatOp<'c>,
        mut annotations: BTreeSet<Annotation>,
    ) -> std::result::Result<FloatAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        2u32.hash(&mut hasher); // Domain separation for floats
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_float()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))?
            .clone())
    }

    fn make_string_annotated(
        &'c self,
        op: StringOp<'c>,
        mut annotations: BTreeSet<Annotation>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        3u32.hash(&mut hasher); // Domain separation for strings
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_string()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))?
            .clone())
    }
}

pub trait HasContext<'c> {
    fn context(&self) -> &'c Context<'c>;
}

impl<'c, T> HasContext<'c> for Arc<T>
where
    T: HasContext<'c>,
{
    fn context(&self) -> &'c Context<'c> {
        self.as_ref().context()
    }
}
