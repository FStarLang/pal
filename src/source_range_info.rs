use std::collections::BTreeMap;
use std::rc::Rc;

use serde::Serialize;

use crate::pass::emit::EmittedModule;

/// A single pulse↔source range mapping.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct RangeMapping {
    pulse_range: lsp_types::Range,
    source_range: lsp_types::Range,
}

/// Info about one emitted .fst module from a given source file.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ModuleInfo {
    fst_file: String,
    decl_name: String,
    source_range: lsp_types::Range,
    mappings: Vec<RangeMapping>,
}

/// Source file entry grouping all modules originating from it.
#[derive(Serialize)]
struct SourceFileInfo {
    uri: String,
    modules: Vec<ModuleInfo>,
}

/// Top-level source range info document.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SourceRangeInfoDoc {
    source_files: Vec<SourceFileInfo>,
}

fn to_module_info(module: &EmittedModule) -> ModuleInfo {
    ModuleInfo {
        fst_file: format!("{}.fst", module.module_name),
        decl_name: module.decl_name.clone(),
        source_range: module.decl_range.to_lsp(),
        mappings: module
            .range_map
            .iter()
            .map(|(loc, pulse_range)| RangeMapping {
                pulse_range: pulse_range.to_lsp(),
                source_range: loc.range.to_lsp(),
            })
            .collect(),
    }
}

fn path_to_uri(path: &str) -> String {
    if path.starts_with('/') {
        format!("file://{}", path)
    } else {
        format!("file:///{}", path)
    }
}

pub fn serialize(modules: &[EmittedModule]) -> String {
    // Group modules by source file, preserving order with BTreeMap
    let mut by_file: BTreeMap<Rc<str>, Vec<&EmittedModule>> = BTreeMap::new();
    for module in modules {
        by_file
            .entry(module.source_file.clone())
            .or_default()
            .push(module);
    }

    let doc = SourceRangeInfoDoc {
        source_files: by_file
            .into_iter()
            .map(|(file, mods)| SourceFileInfo {
                uri: path_to_uri(&file),
                modules: mods.iter().map(|m| to_module_info(m)).collect(),
            })
            .collect(),
    };

    serde_json::to_string_pretty(&doc).unwrap()
}
