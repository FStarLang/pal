use std::collections::HashMap;

use crate::{
    ir::{Location, Position, Range},
    vfs::VFS,
};

impl Position {
    pub fn to_lsp(&self) -> lsp_types::Position {
        // TODO: it's unclear where we get the zero positions from
        lsp_types::Position {
            line: self.line.saturating_sub(1),
            character: self.character.saturating_sub(1),
        }
    }
}

impl Range {
    pub fn to_lsp(&self) -> lsp_types::Range {
        lsp_types::Range {
            start: self.start.to_lsp(),
            end: self.end.to_lsp(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum DiagnosticLevel {
    Warning,
    Error,
}
impl DiagnosticLevel {
    fn is_error(self) -> bool {
        match self {
            DiagnosticLevel::Warning => false,
            DiagnosticLevel::Error => true,
        }
    }
}

impl DiagnosticLevel {
    pub fn to_lsp(self) -> lsp_types::DiagnosticSeverity {
        match self {
            DiagnosticLevel::Warning => lsp_types::DiagnosticSeverity::WARNING,
            DiagnosticLevel::Error => lsp_types::DiagnosticSeverity::ERROR,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Diagnostic {
    pub loc: Location,
    pub level: DiagnosticLevel,
    pub msg: String,
}

impl Diagnostic {
    pub fn to_lsp(&self) -> lsp_types::Diagnostic {
        lsp_types::Diagnostic {
            range: self.loc.range.to_lsp(),
            severity: Some(self.level.to_lsp()),
            code: None,
            code_description: None,
            source: None,
            message: self.msg.clone(),
            related_information: None,
            tags: None,
            data: None,
        }
    }
}

#[derive(Debug)]
pub struct Diagnostics {
    pub diags: Vec<Diagnostic>,
}

impl Diagnostics {
    pub fn empty() -> Self {
        Diagnostics { diags: vec![] }
    }

    pub fn report(&mut self, diag: Diagnostic) {
        self.diags.push(diag)
    }

    pub fn merge(&mut self, other: Diagnostics) {
        self.diags.extend(other.diags);
    }

    pub fn has_errors(&self) -> bool {
        self.diags.iter().any(|d| d.level.is_error())
    }

    pub fn print_to_stderr<'a>(&'a self, vfs: &mut dyn VFS) {
        use codespan_reporting::diagnostic::*;
        use codespan_reporting::term::termcolor::StandardStream;
        use codespan_reporting::{files::Files, term};
        use codespan_reporting::{files::SimpleFiles, term::termcolor::ColorChoice};
        let mut files = SimpleFiles::new();
        let mut file_ids: HashMap<&'a str, usize> = HashMap::new();
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        for diag in &self.diags {
            let mut d = if diag.level == DiagnosticLevel::Error {
                Diagnostic::error()
            } else {
                Diagnostic::warning()
            };
            d = d.with_message(&diag.msg);
            let file_name = &*diag.loc.file_name;
            let file_id = *file_ids.entry(file_name).or_insert_with(|| {
                files.add(
                    file_name,
                    match vfs.read_vfs_file(file_name) {
                        Ok(entry) => entry.contents.clone(),
                        Err(_) => "".to_string(),
                    },
                )
            });
            let pos_to_byte = |pos: Position| {
                files
                    .line_range(file_id, pos.line.saturating_sub(1) as usize)
                    .expect("invalid position")
                    .start
                    + (pos.character.saturating_sub(1) as usize)
            };
            d = d.with_label(Label::primary(
                file_id,
                pos_to_byte(diag.loc.range.start)..(pos_to_byte(diag.loc.range.end) + 1),
            ));
            term::emit_to_io_write(&mut writer.lock(), &config, &files, &d).expect("printing diag");
        }
    }
}
