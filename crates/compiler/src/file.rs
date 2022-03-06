use std::{
    io,
    path::{Path, PathBuf},
    sync::Arc,
};

use notify::{RecursiveMode, Watcher};
use salsa::Durability;

use crate::EntwistleDatabase;

#[salsa::query_group(FileStorage)]
pub trait Files: FileWatcher {
    #[salsa::input]
    fn main(&self) -> PathBuf;
    fn file(&self, path: PathBuf) -> Result<Arc<str>, io::ErrorKind>;
}

fn file(db: &dyn Files, path: PathBuf) -> Result<Arc<str>, io::ErrorKind> {
    db.salsa_runtime().report_synthetic_read(Durability::LOW);
    db.watch(&path);
    let contents = std::fs::read_to_string(&path).map_err(|err| err.kind())?;
    Ok(Arc::from(contents))
}

pub trait FileWatcher {
    fn watch(&self, path: &Path);
    #[allow(clippy::ptr_arg)]
    fn file_changed(&mut self, path: &PathBuf);
}

impl FileWatcher for EntwistleDatabase {
    fn watch(&self, path: &Path) {
        if let Some(watcher) = &self.watcher {
            watcher
                .lock()
                .unwrap()
                .watch(path, RecursiveMode::NonRecursive)
                .unwrap();
        }
    }

    fn file_changed(&mut self, path: &PathBuf) {
        FileQuery.in_db_mut(self).invalidate(path)
    }
}
