use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    ir::{Decl, DeclT},
};

use super::{funcptr_module_name, module_name_for_decl};

/// Generated candidates identify logical modules; explicit include names occupy
/// a separate namespace so even an exact collision can be disambiguated.
pub(super) struct ModuleNames {
    generated: HashMap<String, String>,
}

impl ModuleNames {
    pub(super) fn new(
        diags: &mut Diagnostics,
        decls: &[Decl],
        addr_taken: &HashSet<Rc<str>>,
    ) -> Option<Self> {
        let mut candidates = BTreeSet::new();
        let mut fixed = HashMap::from([(
            "translationerrors".to_string(),
            "TranslationErrors".to_string(),
        )]);
        let mut valid = true;
        for decl in decls {
            if let DeclT::IncludeDecl(include) = &decl.val {
                let name = include.module_name.as_ref();
                let key = name.to_ascii_lowercase();
                if let Some(existing) = fixed.get(&key) {
                    if existing != name || key == "translationerrors" {
                        diags.report(Diagnostic {
                            loc: decl.loc.location().clone(),
                            level: DiagnosticLevel::Error,
                            msg: format!(
                                "explicit module name {name} conflicts with {existing}; \
                                 F* module names are case-insensitive"
                            ),
                        });
                        valid = false;
                    }
                } else {
                    fixed.insert(key, name.to_string());
                }
            } else {
                candidates.insert(module_name_for_decl(decl));
            }

            let fn_decl = match &decl.val {
                DeclT::FnDefn(fd) => Some(&fd.decl),
                DeclT::FnDecl(fd) => Some(fd),
                _ => None,
            };
            if let Some(fd) = fn_decl {
                if !fd.is_pure && addr_taken.contains(&fd.name.val) {
                    candidates.insert(funcptr_module_name(&fd.name.val));
                }
            }
        }
        valid.then(|| Self::allocate(candidates, fixed.into_keys().collect()))
    }

    fn allocate(candidates: BTreeSet<String>, mut used: HashSet<String>) -> Self {
        // Reserve natural names before choosing suffixes, even if their owner
        // sorts later or will itself need renaming.
        let reserved: HashSet<_> = candidates
            .iter()
            .map(|name| name.to_ascii_lowercase())
            .collect();
        let mut generated = HashMap::new();
        for candidate in candidates {
            let mut name = candidate.clone();
            if !used.insert(name.to_ascii_lowercase()) {
                for suffix in 1usize.. {
                    name = format!("{candidate}_{suffix}");
                    let key = name.to_ascii_lowercase();
                    if !reserved.contains(&key) && used.insert(key) {
                        break;
                    }
                }
            }
            generated.insert(candidate, name);
        }
        Self { generated }
    }

    pub(super) fn for_decl(&self, decl: &Decl) -> String {
        let candidate = module_name_for_decl(decl);
        if matches!(decl.val, DeclT::IncludeDecl(_)) {
            candidate
        } else {
            self.generated[&candidate].clone()
        }
    }

    pub(super) fn get(&self, candidate: &str) -> Option<&String> {
        self.generated.get(candidate)
    }

    pub(super) fn for_reference(&self, candidate: String) -> String {
        // References without a generated declaration retain their external
        // module name; only modules owned by this emission can be renamed.
        self.generated.get(&candidate).cloned().unwrap_or(candidate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IncludeDecl, InlinePulseCode, Location, Position, Range, SourceInfo, WithLoc};

    fn allocate(candidates: &[&str], fixed: &[&str]) -> ModuleNames {
        ModuleNames::allocate(
            candidates.iter().map(|name| name.to_string()).collect(),
            fixed.iter().map(|name| name.to_ascii_lowercase()).collect(),
        )
    }

    fn include(name: &str) -> Decl {
        let position = Position {
            line: 1,
            character: 1,
        };
        DeclT::IncludeDecl(IncludeDecl {
            module_name: Rc::from(name),
            code: InlinePulseCode { tokens: Vec::new() },
        })
        .with_loc_core(Rc::new(SourceInfo::Original(Location {
            file_name: Rc::from("module_names.c"),
            range: Range {
                start: position,
                end: position,
            },
        })))
    }

    #[test]
    fn rejects_case_colliding_explicit_names() {
        let mut diags = Diagnostics::empty();
        let decls = [include("Helper"), include("helper")];
        assert!(ModuleNames::new(&mut diags, &decls, &HashSet::new()).is_none());
        assert_eq!(diags.diags.len(), 1);
        assert_eq!(diags.diags[0].loc, *decls[1].loc.location());
        assert!(diags.diags[0].msg.contains("helper conflicts with Helper"));
        assert!(diags.has_errors());
    }

    #[test]
    fn rejects_explicit_translation_errors_module() {
        for name in [
            "TranslationErrors",
            "translationerrors",
            "TRANSLATIONERRORS",
        ] {
            let mut diags = Diagnostics::empty();
            assert!(ModuleNames::new(&mut diags, &[include(name)], &HashSet::new()).is_none());
            assert_eq!(diags.diags.len(), 1);
            assert!(diags.has_errors());
        }
    }

    #[test]
    fn preserves_explicit_names_and_logical_duplicates() {
        let mut diags = Diagnostics::empty();
        let decls = [include("Helper"), include("Helper")];
        let names = ModuleNames::new(&mut diags, &decls, &HashSet::new()).unwrap();
        assert!(!diags.has_errors());
        assert_eq!(names.for_decl(&decls[0]), "Helper");
        assert_eq!(names.for_decl(&decls[1]), "Helper");
    }

    #[test]
    fn preserves_non_colliding_names_and_logical_duplicates() {
        let names = allocate(&["Func_foo", "Func_foo", "Struct_foo"], &[]);
        assert_eq!(names.generated.len(), 2);
        assert_eq!(names.generated["Func_foo"], "Func_foo");
        assert_eq!(names.generated["Struct_foo"], "Struct_foo");
    }

    #[test]
    fn case_collisions_skip_reserved_suffixes() {
        let names = allocate(&["Func_foo", "Func_Foo", "Func_foo_1", "Func_FOO_2"], &[]);
        assert_eq!(names.generated["Func_Foo"], "Func_Foo");
        assert_eq!(names.generated["Func_foo"], "Func_foo_3");
        assert_eq!(names.generated["Func_foo_1"], "Func_foo_1");
        assert_eq!(names.generated["Func_FOO_2"], "Func_FOO_2");
    }

    #[test]
    fn case_collisions_skip_uppercase_suffix_candidate() {
        let names = allocate(&["Func_foo", "Func_Foo", "Func_Foo_1"], &[]);
        assert_eq!(names.generated["Func_Foo"], "Func_Foo");
        assert_eq!(names.generated["Func_Foo_1"], "Func_Foo_1");
        assert_eq!(names.generated["Func_foo"], "Func_foo_2");
    }

    #[test]
    fn fixed_names_take_precedence_even_for_exact_collisions() {
        let names = allocate(
            &["Func_Foo", "Func_foo", "Func_foo_1"],
            &["Func_Foo", "Func_foo_2"],
        );
        assert_eq!(names.generated["Func_Foo"], "Func_Foo_3");
        assert_eq!(names.generated["Func_foo"], "Func_foo_4");
        assert_eq!(names.generated["Func_foo_1"], "Func_foo_1");
    }

    #[test]
    fn allocation_is_order_independent_and_case_insensitively_unique() {
        let candidates = [
            "Func_foo",
            "Func_Foo",
            "Func_FOO",
            "Func_foo_1",
            "Func_Foo_1",
            "Funcptr_foo",
            "Funcptr_Foo",
            "Global_foo",
            "Global_Foo",
        ];
        let forward = allocate(&candidates, &["Func_foo_2"]);
        let reversed: Vec<_> = candidates.into_iter().rev().collect();
        let reverse = allocate(&reversed, &["Func_foo_2"]);
        assert_eq!(forward.generated, reverse.generated);
        let unique: HashSet<_> = forward
            .generated
            .values()
            .map(|name| name.to_ascii_lowercase())
            .collect();
        assert_eq!(unique.len(), candidates.len());
        assert!(!unique.contains("func_foo_2"));
    }
}
