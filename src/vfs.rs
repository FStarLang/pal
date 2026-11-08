use std::{collections::HashMap, path::PathBuf, rc::Rc};

pub fn absolute_file_name(file: &str) -> std::io::Result<String> {
    let name = std::path::absolute(file)?.to_string_lossy().into_owned();
    // Match the spelling used by Clang's FileManager.
    #[cfg(windows)]
    let name = name.replace('\\', "/");
    Ok(name)
}

pub struct VFSEntry {
    pub file_name: String,
    pub contents: String,
}

impl VFSEntry {
    pub fn get_file_name(&self) -> &str {
        &self.file_name
    }
    pub fn get_contents(&self) -> &str {
        &self.contents
    }
}

pub type VFSResult = Result<Rc<VFSEntry>, String>;

pub trait VFS {
    fn read_vfs_file(&mut self, file_name: &str) -> VFSResult;
}

pub struct RealFS {
    cache: HashMap<PathBuf, VFSResult>,
}

impl RealFS {
    pub fn new() -> Self {
        RealFS {
            cache: HashMap::new(),
        }
    }
}

fn read_real_vfs_file(file_name: &str) -> VFSResult {
    let contents = std::fs::read(file_name).map_err(|e| e.to_string())?;
    Ok(Rc::new(VFSEntry {
        file_name: file_name.to_string(),
        contents: String::from_utf8(contents).map_err(|e| e.to_string())?,
    }))
}

impl VFS for RealFS {
    fn read_vfs_file(&mut self, file_name: &str) -> VFSResult {
        // Clang uses entry identity for #pragma once, even when a preinclude
        // and a source include spell the same physical file differently.
        let key = std::fs::canonicalize(file_name).map_err(|e| e.to_string())?;
        if let Some(result) = self.cache.get(&key) {
            return result.clone();
        }
        let result = read_real_vfs_file(file_name);
        self.cache.insert(key, result.clone());
        result
    }
}

pub struct OverlayFS<BaseFS> {
    base: BaseFS,
    overlays: HashMap<String, Rc<VFSEntry>>,
}

impl<BaseFS> OverlayFS<BaseFS> {
    pub fn new(base: BaseFS) -> Self {
        OverlayFS {
            base,
            overlays: HashMap::new(),
        }
    }
    pub fn add_overlay(&mut self, file_name: String, contents: String) {
        self.overlays.insert(
            file_name.clone(),
            Rc::new(VFSEntry {
                file_name,
                contents,
            }),
        );
    }
}

impl<BaseFS: VFS> VFS for OverlayFS<BaseFS> {
    fn read_vfs_file(&mut self, file_name: &str) -> VFSResult {
        match self.overlays.get(file_name) {
            Some(entry) => Ok(entry.clone()),
            None => self.base.read_vfs_file(file_name),
        }
    }
}
