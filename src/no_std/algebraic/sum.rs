use crate::no_std::{algebraic::zero::ParseUnitError, functions::ext::AnyExt};
use core::str::FromStr;
use alloc::vec::Vec;

#[derive(Debug, Clone)]
pub enum TimeUnit {
    Nanos,
    Micros,
    Millis,
    Secs,
}

impl FromStr for TimeUnit {
    type Err = ParseUnitError;

    fn from_str(unit: &str) -> Result<TimeUnit, ParseUnitError> {
        use TimeUnit::*;
        match unit {
            "nanos" => Nanos.into_ok(),
            "micros" => Micros.into_ok(),
            "millis" => Millis.into_ok(),
            "secs" => Secs.into_ok(),
            _ => ParseUnitError.into_err()
        }
    }
}

pub type Map<K, V> = Vec<(K, V)>;

pub trait MapExt<K, V> {
    fn set(&mut self, key: K, value: V) -> Option<V>;
    fn delete(&mut self, key: &K) -> Option<V>;
    fn get(&self, key: &K) -> Option<&V>;
    fn get_mut(&mut self, key: &K) -> Option<&mut V>;
    fn contains_key(&self, key: &K) -> bool;
}

impl<K: PartialEq, V> MapExt<K, V> for Map<K, V> {
    // Adds a key-value pair to the Map. If the key already exist, replaces the value as return value; else (return None).
    fn set(&mut self, key: K, value: V) -> Option<V> {
        for &mut (ref k, ref mut v) in self.iter_mut() {
            if k == &key {
                return Some(std::mem::replace(v, value));
            }
        }
        self.push((key, value));
        None
    }

    // Delete a key from the Map, returning the value at the key if the key was previously in the Map.
    fn delete(&mut self, key: &K) -> Option<V> {
        if let Some(pos) = self.iter().position(|(k, _)| k == key) {
            Some(self.swap_remove(pos).1)
        } else {
            None
        }
    }

    // Returns a reference to the value corresponding to the key.
    fn get(&self, key: &K) -> Option<&V> {
        self.iter().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    // Returns a mutable reference to the value corresponding to the key.
    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.iter_mut().find(|(k, _)| k == key).map(|(_, v)| v)
    }

    // Returns true if the Map contains a value for the specified key.
    fn contains_key(&self, key: &K) -> bool {
        self.iter().any(|(k, _)| k == key)
    }
}