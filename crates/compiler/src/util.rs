use std::fmt;

use crate::Db;

pub trait DisplayWithDb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result;

    fn display<'a>(&'a self, db: &'a dyn Db) -> DbDisplay<'a, Self> {
        DbDisplay { db, value: self }
    }
}

pub struct DbDisplay<'a, T: ?Sized> {
    db: &'a dyn Db,
    value: &'a T,
}

impl<T: DisplayWithDb + ?Sized> fmt::Display for DbDisplay<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f, self.db)
    }
}
