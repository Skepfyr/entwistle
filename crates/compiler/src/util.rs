use std::{collections::HashSet, sync::Arc};

use once_cell::sync::Lazy;
use parking_lot::Mutex;

#[derive(Debug)]
pub struct Interner {
    data: Lazy<Mutex<HashSet<Arc<str>>>>,
}

impl Interner {
    pub const fn new() -> Self {
        Self {
            data: Lazy::new(Mutex::default),
        }
    }

    pub fn intern(&self, value: &str) -> Arc<str> {
        let mut data = self.data.lock();
        match data.get(value) {
            Some(value) => value.clone(),
            None => {
                let value: Arc<str> = value.into();
                data.insert(value.clone());
                value
            }
        }
    }
}
