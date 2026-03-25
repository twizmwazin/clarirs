use ahash::AHasher;
use std::{
    collections::{BTreeSet, HashMap},
    hash::{Hash, Hasher},
    sync::{Arc, RwLock},
};

use crate::{
    cache::{AstCache, Cache},
    prelude::*,
};

/// An interned string that can be cloned cheaply and compared by pointer equality.
#[derive(Clone, Debug, Eq)]
pub struct InternedString(Arc<str>);

impl InternedString {
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
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}

impl Hash for InternedString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
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
#[allow(dead_code)]
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

    pub fn intern_string(&self, s: impl AsRef<str>) -> InternedString {
        let s = s.as_ref();

        {
            let interner = self.string_interner.read().unwrap();
            if let Some(existing) = interner.get(s) {
                return InternedString(Arc::clone(existing));
            }
        }

        let mut interner = self.string_interner.write().unwrap();
        if let Some(existing) = interner.get(s) {
            return InternedString(Arc::clone(existing));
        }

        let arc: Arc<str> = Arc::from(s);
        interner.insert(Arc::clone(&arc), Arc::clone(&arc));
        InternedString(arc)
    }

    pub fn drop_cache(&self, hash: u64) {
        self.ast_cache.drop(hash);
        self.simplification_cache.drop(hash);
        self.excavate_ite_cache.drop(hash);
    }
}

impl<'c> AstFactory<'c> for Context<'c> {
    fn intern_string(&self, s: impl AsRef<str>) -> InternedString {
        self.intern_string(s)
    }

    fn make_annotated(
        &'c self,
        op: Op<'c>,
        mut annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        #[cfg(debug_assertions)]
        op.validate()?;

        let child_annotations: Vec<Annotation> = op
            .child_iter()
            .flat_map(|c| c.annotations().clone())
            .filter(|a| a.relocatable())
            .collect();
        annotations.extend(child_annotations);

        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        self.ast_cache
            .get_or_insert::<ClarirsError>(hash, || {
                Ok(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                )))
            })
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
