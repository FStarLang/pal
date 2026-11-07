use std::collections::BTreeMap;
use std::rc::Rc;

use serde::Serialize;

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

fn path_to_uri(path: &str) -> String {
    if path.starts_with('/') {
        format!("file://{}", path)
    } else {
        format!("file:///{}", path)
    }
}

/// The emitter produces one module per C declaration and no token-level
/// range map. The declaration's own range is
/// all there is to report, and it is what an IDE needs to get from a generated
/// file back to the code that produced it; `mappings` is empty rather than
/// approximate, because a wrong position inside a module is worse than none.
pub fn serialize(modules: &[crate::pass::emit_palow::PalowModule]) -> String {
    let mut by_file: BTreeMap<Rc<str>, Vec<&crate::pass::emit_palow::PalowModule>> =
        BTreeMap::new();
    for module in modules {
        let Some(o) = &module.origin else { continue };
        by_file.entry(o.file.clone()).or_default().push(module);
    }

    let doc = SourceRangeInfoDoc {
        source_files: by_file
            .into_iter()
            .map(|(file, mods)| SourceFileInfo {
                uri: path_to_uri(&file),
                modules: mods
                    .iter()
                    .map(|m| {
                        let o = m.origin.as_ref().unwrap();
                        ModuleInfo {
                            fst_file: format!("{}.fst", m.module_name),
                            decl_name: o.name.clone(),
                            source_range: o.range.to_lsp(),
                            mappings: Vec::new(),
                        }
                    })
                    .collect(),
            })
            .collect(),
    };

    serde_json::to_string_pretty(&doc).unwrap()
}
