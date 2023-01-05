use tokio::sync::Mutex;

pub trait AsyncExt: Sized {
    /// Convert `value` to `Mutex::new(value)`
    fn into_mutex(self) -> Mutex<Self> {
        Mutex::new(self)
    }
}

impl<T> AsyncExt for T {}