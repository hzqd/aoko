pub trait KtStd {
    fn drop(self) where Self: Sized {}

    fn then<R>(self, f: impl FnOnce(Self) -> R) -> R where Self: Sized {
        f(self)
    }

    fn also<R>(self, f: impl FnOnce(&Self) -> R) -> Self where Self: Sized {
        f(&self);
        self
    }
    
    fn also_mut<R>(mut self, f: impl FnOnce(&mut Self) -> R) -> Self where Self: Sized {
        f(&mut self);
        self
    }

    fn sout(self) -> Self where Self: Sized + std::fmt::Debug {
        self.also(|s| println!("{:#?}", s))
    }

    fn echo(self) -> Self where Self: Sized + std::fmt::Debug {
        self.also(|s| println!("{:?}", s))
    }
}

impl<T> KtStd for T {}

trait FnOnceExt<P1, P2, R> {
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R>;
}

impl<P1, P2: 'static, R, F> FnOnceExt<P1, P2, R> for F where F: FnOnce(P1, P2) -> R + 'static {
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R> {
        Box::new(move |p1| self(p1, p2))
    }
}

pub trait IterExt<T> {
    fn on_each(self, f: impl Fn(&mut T)) -> Self;
    fn filter(self, f: impl Fn(&T) -> bool) -> Vec<T>;
}

impl<T> IterExt<T> for Vec<T> {
    fn on_each(self, f: impl Fn(&mut T)) -> Self {
        self.also_mut(|v| v.iter_mut().for_each(f))
    }

    fn filter(self, f: impl Fn(&T) -> bool) -> Vec<T> {
        self.into_iter().filter(f).collect()
    }
}

pub trait VecExt<T, R> {
    fn map(&self, f: impl Fn(&T) -> R) -> Vec<R>;
    fn filter_map(&self, f: impl Fn(&T) -> Option<R>) -> Vec<R>;
    fn fold(&self, init: R, f: impl Fn(R, &T) -> R) -> R;
    fn reduce(&self, f: impl Fn(R, &T) -> R) -> R where R: Default;
}

impl<T, R> VecExt<T, R> for Vec<T> {
    fn map(&self, f: impl Fn(&T) -> R) -> Vec<R> {
        self.iter().map(f).collect()
    }

    fn filter_map(&self, f: impl Fn(&T) -> Option<R>) -> Vec<R> {
        self.iter().filter_map(f).collect()
    }

    fn fold(&self, init: R, f: impl Fn(R, &T) -> R) -> R {
        self.iter().fold(init, f)
    }

    fn reduce(&self, f: impl Fn(R, &T) -> R) -> R where R: Default {
        self.iter().fold(R::default(), f)
    }
}