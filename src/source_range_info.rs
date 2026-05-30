use std::collections::BTreeMap;
use std::rc::Rc;

use serde::Serialize;

use crate::pass::emit::EmittedModule;

/// A single source↔pulse position mapping.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct PositionMapping {
    source: lsp_types::Position,
    pulse: lsp_types::Position,
}

/// Info about one emitted .fst module from a given source file.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ModuleInfo {
    fst_file: String,
    decl_name: String,
    source_range: lsp_types::Range,
    mappings: Vec<PositionMapping>,
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
    // Collect (begin,begin) and (end,end) position pairs, filtering to
    // only mappings whose source location is in the module's own source file.
    let source_file = &module.source_file;
    let mut mappings: Vec<PositionMapping> = module
        .range_map
        .iter()
        .filter(|(loc, _)| loc.file_name == *source_file)
        .flat_map(|(loc, pulse_range)| {
            [
                PositionMapping {
                    source: loc.range.start.to_lsp(),
                    pulse: pulse_range.start.to_lsp(),
                },
                PositionMapping {
                    source: loc.range.end.to_lsp(),
                    pulse: pulse_range.end.to_lsp(),
                },
            ]
        })
        .collect();

    // Sort by source position (line first, then character)
    mappings.sort_by(|a, b| {
        a.source
            .line
            .cmp(&b.source.line)
            .then(a.source.character.cmp(&b.source.character))
    });

    // Deduplicate by source position (keep first occurrence)
    mappings.dedup_by(|b, a| {
        a.source.line == b.source.line && a.source.character == b.source.character
    });

    ModuleInfo {
        fst_file: format!("{}.fst", module.module_name),
        decl_name: module.decl_name.clone(),
        source_range: module.decl_range.to_lsp(),
        mappings,
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
