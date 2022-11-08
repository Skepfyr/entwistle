use std::fmt;

pub trait DbDisplay<Db: ?Sized> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result;
    fn display<'a>(&'a self, db: &'a Db) -> DbDisplayWrapper<'a, Self, Db> {
        DbDisplayWrapper(self, db)
    }
}

impl<Db: ?Sized, T: DbDisplay<Db>> DbDisplay<Db> for Option<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        match self {
            Some(item) => {
                write!(f, "Some({})", item.display(db))
            }
            None => f.write_str("None"),
        }
    }
}

#[derive(Clone, Copy)]
pub struct DbDisplayWrapper<'a, T: ?Sized, Db: ?Sized>(&'a T, &'a Db);

impl<'a, T, Db> fmt::Display for DbDisplayWrapper<'a, T, Db>
where
    T: DbDisplay<Db>,
    Db: ?Sized,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f, self.1)
    }
}
