#[macro_export]
macro_rules! add_pyfunctions {
    ($m:ident, $($fn_name:path),*,) => {
        $(
            $m.add_function(wrap_pyfunction!($fn_name, $m)?)?;
        )*
    };
}

/// Generates the common `impl` block (constructors + cache) and a `#[pymethods]` block
/// containing all shared getters, annotation methods, and utility methods for a PyO3 AST
/// wrapper type.
///
/// # Parameters
///
/// - `$type`: The concrete PyO3 struct (e.g. `Bool`, `BV`, `FP`, `PyAstString`)
/// - `$inner_type`: The inner Rust AST type (e.g. `BoolAst<'static>`)
/// - `$cache`: Name of the static `DashMap` cache variable
/// - `$simplify`: Expression to simplify the inner value in the constructor
/// - `$make_annotated`: Factory method name on context for annotated nodes
/// - `$make_clear`: Factory method name on context for un-annotated nodes
/// - `$dynast_variant`: The `DynAst` enum variant name
/// - `$dynast_into`: Method on `DynAst` to extract the inner type
/// - `$canon_name`: Human-readable name for error messages
/// - Init chain: either `Base => $type` (2-level) or `Base => $mid => $type` (3-level)
#[macro_export]
macro_rules! impl_py_ast_common {
    // 2-level init chain: Base -> Type (Bool, PyAstString)
    (
        type: $type:ident,
        inner_type: $inner_type:ty,
        cache: $cache:ident,
        simplify: |$simp_var:ident| $simplify:expr,
        make_annotated: $make_annotated:ident,
        make_clear: $make_clear:ident,
        dynast_variant: $dynast_variant:ident,
        dynast_into: $dynast_into:ident,
        canon_name: $canon_name:expr,
        init_chain: Base => $type2:ident,
    ) => {
        impl $type {
            pub fn new<'py>(
                py: Python<'py>,
                inner: &$inner_type,
            ) -> Result<Bound<'py, $type>, ClaripyError> {
                Self::new_with_name(py, inner, None)
            }

            pub fn new_with_name<'py>(
                py: Python<'py>,
                inner: &$inner_type,
                name: Option<String>,
            ) -> Result<Bound<'py, $type>, ClaripyError> {
                use pyo3::types::{PyWeakrefMethods, PyWeakrefReference};
                let $simp_var = inner;
                let inner: &$inner_type = &$simplify;
                if let Some(cache_hit) = $cache.get(&inner.hash()).and_then(|cache_hit| {
                    cache_hit
                        .bind(py)
                        .upgrade_as::<$type>()
                        .expect(concat!(stringify!($type), " cache poisoned"))
                }) {
                    Ok(cache_hit)
                } else {
                    let this = Bound::new(
                        py,
                        PyClassInitializer::from(Base::new_with_name(py, name)).add_subclass(
                            $type {
                                inner: inner.clone(),
                            },
                        ),
                    )?;
                    let weakref = PyWeakrefReference::new(&this)?;
                    $cache.insert(inner.hash(), weakref.unbind());
                    Ok(this)
                }
            }
        }

        $crate::impl_py_ast_pymethods!(
            $type,
            $inner_type,
            $make_annotated,
            $make_clear,
            $dynast_variant,
            $dynast_into,
            $canon_name
        );
    };

    // 3-level init chain: Base -> Mid -> Type (BV, FP)
    (
        type: $type:ident,
        inner_type: $inner_type:ty,
        cache: $cache:ident,
        simplify: |$simp_var:ident| $simplify:expr,
        make_annotated: $make_annotated:ident,
        make_clear: $make_clear:ident,
        dynast_variant: $dynast_variant:ident,
        dynast_into: $dynast_into:ident,
        canon_name: $canon_name:expr,
        init_chain: Base => $mid:ident => $type2:ident,
    ) => {
        impl $type {
            pub fn new<'py>(
                py: Python<'py>,
                inner: &$inner_type,
            ) -> Result<Bound<'py, $type>, ClaripyError> {
                Self::new_with_name(py, inner, None)
            }

            pub fn new_with_name<'py>(
                py: Python<'py>,
                inner: &$inner_type,
                name: Option<String>,
            ) -> Result<Bound<'py, $type>, ClaripyError> {
                use pyo3::types::{PyWeakrefMethods, PyWeakrefReference};
                let $simp_var = inner;
                let inner: &$inner_type = &$simplify;
                if let Some(cache_hit) = $cache.get(&inner.hash()).and_then(|cache_hit| {
                    cache_hit
                        .bind(py)
                        .upgrade_as::<$type>()
                        .expect(concat!(stringify!($type), " cache poisoned"))
                }) {
                    Ok(cache_hit)
                } else {
                    let this = Bound::new(
                        py,
                        PyClassInitializer::from(Base::new_with_name(py, name))
                            .add_subclass($mid)
                            .add_subclass($type {
                                inner: inner.clone(),
                            }),
                    )?;
                    let weakref = PyWeakrefReference::new(&this)?;
                    $cache.insert(inner.hash(), weakref.unbind());
                    Ok(this)
                }
            }
        }

        $crate::impl_py_ast_pymethods!(
            $type,
            $inner_type,
            $make_annotated,
            $make_clear,
            $dynast_variant,
            $dynast_into,
            $canon_name
        );
    };
}

/// Internal helper macro — use `impl_py_ast_common!` instead.
#[macro_export]
macro_rules! impl_py_ast_pymethods {
    (
        $type:ident, $inner_type:ty,
        $make_annotated:ident, $make_clear:ident,
        $dynast_variant:ident, $dynast_into:ident,
        $canon_name:expr
    ) => {
        #[pymethods]
        impl $type {
            // ── Getters ──────────────────────────────────────────────

            #[getter]
            pub fn op(&self) -> String {
                self.inner.to_opstring()
            }

            #[getter]
            pub fn args<'py>(
                &self,
                py: Python<'py>,
            ) -> Result<Vec<Bound<'py, PyAny>>, ClaripyError> {
                self.inner.extract_py_args(py)
            }

            #[getter]
            pub fn variables<'py>(
                &self,
                py: Python<'py>,
            ) -> Result<Bound<'py, pyo3::types::PyFrozenSet>, ClaripyError> {
                Ok(pyo3::types::PyFrozenSet::new(
                    py,
                    self.inner
                        .variables()
                        .iter()
                        .map(|v| v.as_str().into_py_any(py))
                        .collect::<Result<Vec<_>, _>>()?
                        .iter(),
                )?)
            }

            #[getter]
            pub fn symbolic(&self) -> bool {
                self.inner.symbolic()
            }

            #[getter]
            pub fn concrete(&self) -> bool {
                !self.inner.symbolic()
            }

            #[getter]
            pub fn annotations(&self) -> PyResult<Vec<PyAnnotation>> {
                Ok(self
                    .inner
                    .annotations()
                    .iter()
                    .cloned()
                    .map(PyAnnotation::from)
                    .collect())
            }

            pub fn hash(&self) -> u64 {
                self.inner.hash()
            }

            pub fn __hash__(&self) -> usize {
                self.hash() as usize
            }

            pub fn __repr__(&self) -> String {
                use clarirs_core::smtlib::ToSmtLib;
                self.inner.to_smtlib()
            }

            #[getter]
            pub fn depth(&self) -> u32 {
                self.inner.depth()
            }

            pub fn is_leaf(&self) -> bool {
                self.inner.depth() == 1
            }

            // ── Core methods ─────────────────────────────────────────

            #[allow(clippy::type_complexity)]
            pub fn canonicalize<'py>(
                &self,
                py: Python<'py>,
            ) -> Result<
                (
                    std::collections::HashMap<u64, Bound<'py, PyAny>>,
                    usize,
                    Bound<'py, $type>,
                ),
                ClaripyError,
            > {
                use clarirs_core::algorithms::canonicalize;
                let (replacement_map, counter, canonical) =
                    canonicalize(&self.inner.clone().into())?;
                let canonical_node = $type::new(
                    py,
                    &canonical
                        .$dynast_into()
                        .ok_or(ClaripyError::InvalidOperation(
                            concat!("Canonicalization did not produce a ", $canon_name).to_string(),
                        ))?,
                )?;

                let mut py_map = std::collections::HashMap::new();
                for (hash, dynast) in replacement_map {
                    let py_ast = Base::from_dynast(py, dynast)?;
                    py_map.insert(hash, py_ast.into_any());
                }

                Ok((py_map, counter, canonical_node))
            }

            pub fn identical(&self, other: Bound<'_, Base>) -> Result<bool, ClaripyError> {
                use clarirs_core::algorithms::structurally_match;
                let other_dyn = Base::to_dynast(other)?;
                Ok(structurally_match(
                    &DynAst::$dynast_variant(self.inner.clone()),
                    &other_dyn,
                )?)
            }

            #[pyo3(signature = (respect_annotations=true))]
            pub fn simplify<'py>(
                &self,
                py: Python<'py>,
                respect_annotations: bool,
            ) -> Result<Bound<'py, $type>, ClaripyError> {
                $type::new(py, &self.inner.simplify_ext(respect_annotations, false)?)
            }

            pub fn replace<'py>(
                &self,
                py: Python<'py>,
                from: Bound<'py, Base>,
                to: Bound<'py, Base>,
            ) -> Result<Bound<'py, $type>, ClaripyError> {
                use clarirs_core::algorithms::Replace;
                let from_ast = Base::to_dynast(from)?;
                let to_ast = Base::to_dynast(to)?;
                let replaced = self.inner.replace(&from_ast, &to_ast)?;
                $type::new(py, &replaced)
            }

            #[allow(clippy::type_complexity)]
            pub fn __reduce__<'py>(
                &self,
                py: Python<'py>,
            ) -> Result<
                (
                    Bound<'py, PyAny>,
                    (String, Vec<Bound<'py, PyAny>>, Vec<PyAnnotation>),
                ),
                ClaripyError,
            > {
                let class = py.get_type::<$type>();
                let op = self.op();
                let args = self.args(py)?;
                let annotations = self.annotations()?;
                Ok((class.into_any(), (op, args, annotations)))
            }

            // ── Annotation methods ───────────────────────────────────

            pub fn has_annotation_type(
                &self,
                annotation_type: PyAnnotationType,
            ) -> Result<bool, ClaripyError> {
                Ok(self
                    .annotations()?
                    .iter()
                    .any(|annotation| annotation_type.matches(annotation.0.type_())))
            }

            pub fn get_annotations_by_type(
                &self,
                annotation_type: PyAnnotationType,
            ) -> Result<Vec<PyAnnotation>, ClaripyError> {
                Ok(self
                    .annotations()?
                    .into_iter()
                    .filter(|annotation| annotation_type.matches(annotation.0.type_()))
                    .collect())
            }

            pub fn get_annotation(
                &self,
                annotation_type: PyAnnotationType,
            ) -> Result<Option<PyAnnotation>, ClaripyError> {
                Ok(self
                    .annotations()?
                    .into_iter()
                    .find(|annotation| annotation_type.matches(annotation.0.type_())))
            }

            pub fn append_annotation<'py>(
                &self,
                py: Python<'py>,
                annotation: PyAnnotation,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let new_annotations = self
                    .inner
                    .annotations()
                    .iter()
                    .cloned()
                    .chain([annotation.0.clone()]);
                Self::new(py, &GLOBAL_CONTEXT.annotate(&self.inner, new_annotations)?)
            }

            pub fn append_annotations<'py>(
                &self,
                py: Python<'py>,
                annotations: Vec<PyAnnotation>,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let new_annotations = self
                    .inner
                    .annotations()
                    .iter()
                    .cloned()
                    .chain(annotations.into_iter().map(|a| a.0));
                Self::new(py, &GLOBAL_CONTEXT.annotate(&self.inner, new_annotations)?)
            }

            #[pyo3(signature = (*annotations, remove_annotations = None))]
            pub fn annotate<'py>(
                &self,
                py: Python<'py>,
                annotations: Vec<PyAnnotation>,
                remove_annotations: Option<Vec<PyAnnotation>>,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let new_annotations = self
                    .annotations()?
                    .iter()
                    .filter(|a| {
                        if let Some(remove_annotations) = &remove_annotations {
                            !remove_annotations.iter().any(|ra| ra.0 == a.0)
                        } else {
                            true
                        }
                    })
                    .map(|a| a.0.clone())
                    .chain(annotations.into_iter().map(|a| a.0))
                    .collect();
                let inner = self
                    .inner
                    .context()
                    .$make_annotated(self.inner.op().clone(), new_annotations)?;
                Self::new(py, &inner)
            }

            pub fn insert_annotations<'py>(
                &self,
                py: Python<'py>,
                annotations: Vec<PyAnnotation>,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                Self::new(
                    py,
                    &GLOBAL_CONTEXT.annotate(&self.inner, annotations.into_iter().map(|a| a.0))?,
                )
            }

            /// This actually just removes all annotations and adds the new ones.
            pub fn replace_annotations<'py>(
                &self,
                py: Python<'py>,
                annotations: Vec<PyAnnotation>,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let inner = self.inner.context().$make_annotated(
                    self.inner.op().clone(),
                    annotations.into_iter().map(|a| a.0).collect(),
                )?;
                Self::new(py, &inner)
            }

            pub fn remove_annotation<'py>(
                &self,
                py: Python<'py>,
                annotation: PyAnnotation,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let inner = self.inner.context().$make_annotated(
                    self.inner.op().clone(),
                    self.inner
                        .annotations()
                        .iter()
                        .filter(|a| **a != annotation.0)
                        .cloned()
                        .collect(),
                )?;
                Self::new(py, &inner)
            }

            pub fn remove_annotations<'py>(
                &self,
                py: Python<'py>,
                annotations: Vec<PyAnnotation>,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let annotations_set: std::collections::BTreeSet<_> =
                    annotations.into_iter().map(|a| a.0).collect();
                let inner = self.inner.context().$make_annotated(
                    self.inner.op().clone(),
                    self.inner
                        .annotations()
                        .iter()
                        .filter(|a| !annotations_set.contains(a))
                        .cloned()
                        .collect(),
                )?;
                Self::new(py, &inner)
            }

            pub fn clear_annotations<'py>(
                &self,
                py: Python<'py>,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let inner = self.inner.context().$make_clear(self.inner.op().clone())?;
                Self::new(py, &inner)
            }

            pub fn clear_annotation_type<'py>(
                &self,
                py: Python<'py>,
                annotation_type: PyAnnotationType,
            ) -> Result<Bound<'py, Self>, ClaripyError> {
                let inner = self.inner.context().$make_annotated(
                    self.inner.op().clone(),
                    self.inner
                        .annotations()
                        .iter()
                        .filter(|a| !annotation_type.matches(a.type_()))
                        .cloned()
                        .collect(),
                )?;
                Self::new(py, &inner)
            }
        }
    };
}
