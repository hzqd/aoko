use std::{fmt::Debug, ops::Add, iter::Product};
use rayon::{iter::Either, prelude::*};

pub trait KtStd<R>: Sized {
    fn let_ref<'a>(&'a self, f: impl FnOnce(&'a Self) -> R) -> R {
        f(self)
    }

    fn let_mut<'a>(&'a mut self, f: impl FnOnce(&'a mut Self) -> R) -> R {
        f(self)
    }

    fn let_owned(self, f: impl FnOnce(Self) -> R) -> R {
        f(self)
    }

    fn also_ref(self, f: impl FnOnce(&Self) -> R) -> Self {
        f(&self);
        self
    }
    
    fn also_mut(mut self, f: impl FnOnce(&mut Self) -> R) -> Self {
        f(&mut self);
        self
    }
}

impl<T, R> KtStd<R> for T {}

pub trait Ext: Sized {
    fn drop(self) {}

    fn sout(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:#?}", s))
    }

    fn echo(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:?}", s))
    }

    fn type_name(&self) -> &str {
        std::any::type_name::<Self>()
    }
    
    fn type_size(&self) -> usize {
        std::mem::size_of::<Self>()
    }
}

impl<T> Ext for T {}

trait FnOnceExt<P1, P2, R> {
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R>;
}

impl<P1, P2: 'static, R, F> FnOnceExt<P1, P2, R> for F where F: FnOnce(P1, P2) -> R + 'static {
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R> {
        Box::new(move |p1| self(p1, p2))
    }
}

pub trait Sort<T> {
    fn sort(self) -> Vec<T>;
}

impl<T: Ord + Send> Sort<T> for Vec<T> {
    fn sort(self) -> Vec<T> {
        self.also_mut(|v| v.par_sort())
    }
}

pub trait VecExt2<T, R> {
    fn map(&self, f: impl Fn(&T) -> R + Sync + Send) -> Vec<R>;
    fn filter_map(&self, f: impl Fn(&T) -> Option<R> + Sync + Send) -> Vec<R>;
}

impl<T, R> VecExt2<T, R> for Vec<T> where T: Sync, R: Send {
    fn map(&self, f: impl Fn(&T) -> R + Sync + Send) -> Vec<R> {
        self.par_iter().map(f).collect()
    }

    fn filter_map(&self, f: impl Fn(&T) -> Option<R> + Sync + Send) -> Vec<R> {
        self.par_iter().filter_map(f).collect()
    }
}

pub trait VecExt1<T> {
    fn for_each(self, f: impl Fn(T) + Sync + Send);
    fn on_each(self, f: impl Fn(&mut T) + Sync + Send) -> Self;
    fn filter(self, f: impl Fn(&T) -> bool + Sync + Send) -> Vec<T>;
    fn fold(self, init: T, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy;
    fn reduce(self, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy + Default;
    fn sum(self) -> T where T: Sync + Copy + Default + Add<Output = T>;
    fn product(self) -> T where T: Product;
    fn partition(self, f: impl Fn(&T) -> bool + Sync + Send) -> (Vec<T>, Vec<T>);
    fn partition3<F>(self, predicate1: F, predicate2: F) -> (Vec<T>, Vec<T>, Vec<T>) where T: Sync, F: Fn(&T) -> bool + Sync + Send;
}

impl<T> VecExt1<T> for Vec<T> where T: Send {
    fn for_each(self, f: impl Fn(T) + Sync + Send) {
        self.into_par_iter().for_each(f);
    }

    fn on_each(self, f: impl Fn(&mut T) + Sync + Send) -> Self {
        self.also_mut(|v| v.par_iter_mut().for_each(f))
    }

    fn filter(self, f: impl Fn(&T) -> bool + Sync + Send) -> Vec<T> {
        self.into_par_iter().filter(f).collect()
    }

    fn fold(self, init: T, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy {
        self.into_par_iter().reduce(|| init, f)
    }

    fn reduce(self, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy + Default {
        self.fold(T::default(), f)
    }

    fn sum(self) -> T where T: Sync + Copy + Default + Add<Output = T> {
        self.reduce(|a, b| a + b)
    }

    fn product(self) -> T where T: Product {
        self.into_par_iter().product()
    }

    fn partition(self, f: impl Fn(&T) -> bool + Sync + Send) -> (Vec<T>, Vec<T>) {
        self.into_par_iter().partition(f)
    }

    fn partition3<F>(self, predicate1: F, predicate2: F) -> (Vec<T>, Vec<T>, Vec<T>) where T: Sync, F: Fn(&T) -> bool + Sync + Send {
        let ((first, second), third) = self.into_par_iter().partition_map(|e|
            if predicate1(&e) { Either::Left(Either::Left(e)) }
            else if predicate2(&e) { Either::Left(Either::Right(e)) }
            else { Either::Right(e) }
        );
        (first, second, third)
    }
}