use std::{collections::HashMap, rc::Rc};

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
    cache: HashMap<String, VFSResult>,
}

impl RealFS {
    pub fn new() -> Self {
        RealFS {
            cache: HashMap::new(),
        }
    }
}

fn read_real_vfs_file(file_name: &str) -> VFSResult {
    // let canon_file_name = std::fs::canonicalize(file_name).map_err(|e| e.to_string())?;
    let contents = std::fs::read(file_name).map_err(|e| e.to_string())?;
    Ok(Rc::new(VFSEntry {
        file_name: file_name.to_string(),
        contents: String::from_utf8(contents).map_err(|e| e.to_string())?,
    }))
}

impl VFS for RealFS {
    fn read_vfs_file(&mut self, file_name: &str) -> VFSResult {
        if let Some(result) = self.cache.get(file_name) {
            return result.clone();
        }
        let result = read_real_vfs_file(file_name);
        self.cache.insert(file_name.to_string(), result.clone());
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
