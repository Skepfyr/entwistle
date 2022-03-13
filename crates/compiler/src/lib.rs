use std::{path::PathBuf, sync::Mutex};

use notify::RecommendedWatcher;
use salsa::{Database, Durability, Storage};

use crate::{
    file::{FileStorage, Files},
    language::LanguageStorage,
    lower::LowerStorage,
    parse_table::ParseTableStorage,
};

macro_rules! intern_key {
    ($($name:ident),+) => {$(
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub salsa::InternId);

        impl ::salsa::InternKey for $name {
            fn from_intern_id(v: ::salsa::InternId) -> Self {
                Self(v)
            }

            fn as_intern_id(&self) -> ::salsa::InternId {
                self.0
            }
        }
    )+};
}

pub mod file;
pub mod language;
pub mod lower;
pub mod parse_table;
pub mod util;

#[salsa::database(FileStorage, LanguageStorage, LowerStorage, ParseTableStorage)]
pub struct EntwistleDatabase {
    storage: Storage<Self>,
    watcher: Option<Mutex<RecommendedWatcher>>,
}

impl Database for EntwistleDatabase {}

impl EntwistleDatabase {
    pub fn oneshot(main: PathBuf) -> Self {
        let mut db = EntwistleDatabase {
            storage: salsa::Storage::default(),
            watcher: None,
        };
        db.set_main_with_durability(main, Durability::MEDIUM);
        db
    }
}
