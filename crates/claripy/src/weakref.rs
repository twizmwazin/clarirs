use pyo3::{
    ffi::{self},
    Py, Python,
};

pub struct WeakRef(*mut ffi::PyObject);

unsafe impl Send for WeakRef {}
unsafe impl Sync for WeakRef {}

impl WeakRef {
    pub fn is_valid(&self) -> bool {
        unsafe { ffi::PyWeakref_CheckRef(self.0) != 0 }
    }

    pub fn upgrade<T>(&self, py: Python<'_>) -> Option<Py<T>> {
        if self.is_valid() {
            Some(unsafe { Py::from_borrowed_ptr(py, ffi::PyWeakref_GetObject(self.0)) })
        } else {
            None
        }
    }
}

impl<T> From<&Py<T>> for WeakRef {
    fn from(obj: &Py<T>) -> Self {
        WeakRef(unsafe { ffi::PyWeakref_NewRef(obj.as_ptr(), std::ptr::null_mut()) })
    }
}
