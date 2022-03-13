use std::fmt;

pub trait DbDisplay<Db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result;
    fn display<'a>(&'a self, db: &'a Db) -> DbDisplayWrapper<'a, Self, Db> {
        DbDisplayWrapper(self, db)
    }
}

#[derive(Clone, Copy)]
pub struct DbDisplayWrapper<'a, T: ?Sized, Db: ?Sized>(&'a T, &'a Db);

impl<'a, T, Db> fmt::Display for DbDisplayWrapper<'a, T, Db>
where
    T: DbDisplay<Db>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f, self.1)
    }
}
