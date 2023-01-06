use crate::no_std::functions::ext::FnOnceExt;

use alloc::sync::Arc;
use tokio::sync::Mutex;

pub trait AsyncExt: Sized {
    /// Convert `value` to `tokio::sync::Mutex::new(value)`
    fn into_tokio_mutex(self) -> Mutex<Self> {
        Mutex::new(self)
    }

    /// Convert `self` to `tokio`'s `Arc<Mutex<Self>>`
    fn into_tokio_arc_mutex(self) -> Arc<Mutex<Self>> {
        Arc::new.compose(Mutex::new)(self)
    }
}

impl<T> AsyncExt for T {}