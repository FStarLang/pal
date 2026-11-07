//! Case-insensitive allocation of generated module names.
//!
//! C distinguishes `foo` from `Foo`, but F* resolves a module to a file in a
//! case-insensitive way, so `Func_foo` and `Func_Foo` are the same module to
//! it. Every generated module name is a candidate; colliding candidates are
//! given numeric suffixes before any text is turned into a module.

use std::collections::{BTreeSet, HashMap, HashSet};

/// Generated candidates identify logical modules; explicit include names
/// occupy a separate namespace so even an exact collision can be
/// disambiguated.
pub(super) struct ModuleNames {
    generated: HashMap<String, String>,
}

impl ModuleNames {
    /// `fixed` are names that cannot change: `_include_pulse` modules and
    /// `TranslationErrors`. Returns the names of the explicit modules that
    /// collide case-insensitively with another fixed name.
    pub(super) fn new<'a>(
        candidates: impl IntoIterator<Item = &'a str>,
        explicit: impl IntoIterator<Item = &'a str>,
    ) -> (Self, Vec<(String, String)>) {
        let mut fixed = HashMap::from([(
            "translationerrors".to_string(),
            "TranslationErrors".to_string(),
        )]);
        let mut conflicts = Vec::new();
        for name in explicit {
            let key = name.to_ascii_lowercase();
            match fixed.get(&key) {
                Some(existing) if existing != name || key == "translationerrors" => {
                    conflicts.push((name.to_string(), existing.clone()));
                }
                Some(_) => {}
                None => {
                    fixed.insert(key, name.to_string());
                }
            }
        }
        let candidates = candidates.into_iter().map(str::to_string).collect();
        (
            Self::allocate(candidates, fixed.into_keys().collect()),
            conflicts,
        )
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

    pub(super) fn get<'a>(&'a self, candidate: &'a str) -> &'a str {
        self.generated
            .get(candidate)
            .map(String::as_str)
            .unwrap_or(candidate)
    }

    /// Rewrites qualified references `M.x` to a renamed generated module `M`,
    /// except for the names in `keep`. No allocated name is itself a renamed
    /// candidate, so the rewrite is idempotent.
    pub(super) fn rewrite_references(&self, code: &str, keep: &HashSet<&str>) -> String {
        if self.generated.iter().all(|(k, v)| k == v) {
            return code.to_string();
        }
        let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
        let mut out = String::with_capacity(code.len());
        let mut word = String::new();
        let mut prev: Option<char> = None;
        let mut chars = code.chars().peekable();
        while let Some(c) = chars.next() {
            if is_ident(c) {
                if word.is_empty() && prev == Some('.') {
                    // The tail of a qualified name is never a module of ours.
                    word.push('\0');
                }
                word.push(c);
                continue;
            }
            if !word.is_empty() {
                let qualified_tail = word.starts_with('\0');
                let w = word.trim_start_matches('\0');
                let next_ident = c == '.' && chars.peek().is_some_and(|n| is_ident(*n));
                match self.generated.get(w) {
                    Some(new) if next_ident && !qualified_tail && !keep.contains(w) => out += new,
                    _ => out += w,
                }
                word.clear();
            }
            out.push(c);
            prev = Some(c);
        }
        out += word.trim_start_matches('\0');
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn allocate(candidates: &[&str], fixed: &[&str]) -> ModuleNames {
        ModuleNames::allocate(
            candidates.iter().map(|name| name.to_string()).collect(),
            fixed.iter().map(|name| name.to_ascii_lowercase()).collect(),
        )
    }

    #[test]
    fn rejects_case_colliding_explicit_names() {
        let (_, conflicts) = ModuleNames::new([], ["Helper", "helper", "Helper"]);
        assert_eq!(
            conflicts,
            vec![("helper".to_string(), "Helper".to_string())]
        );
        for name in ["TranslationErrors", "TRANSLATIONERRORS"] {
            let (_, conflicts) = ModuleNames::new([], [name]);
            assert_eq!(conflicts.len(), 1);
        }
    }

    #[test]
    fn preserves_non_colliding_names() {
        let names = allocate(&["Func_foo", "Func_foo", "Struct_foo"], &[]);
        assert_eq!(names.generated.len(), 2);
        assert_eq!(names.get("Func_foo"), "Func_foo");
        assert_eq!(names.get("Struct_foo"), "Struct_foo");
    }

    #[test]
    fn case_collisions_skip_reserved_suffixes() {
        let names = allocate(&["Func_foo", "Func_Foo", "Func_foo_1", "Func_FOO_2"], &[]);
        assert_eq!(names.get("Func_Foo"), "Func_Foo");
        assert_eq!(names.get("Func_foo"), "Func_foo_3");
        assert_eq!(names.get("Func_foo_1"), "Func_foo_1");
        assert_eq!(names.get("Func_FOO_2"), "Func_FOO_2");
    }

    #[test]
    fn fixed_names_take_precedence_even_for_exact_collisions() {
        let names = allocate(
            &["Func_Foo", "Func_foo", "Func_foo_1"],
            &["Func_Foo", "Func_foo_2"],
        );
        assert_eq!(names.get("Func_Foo"), "Func_Foo_3");
        assert_eq!(names.get("Func_foo"), "Func_foo_4");
        assert_eq!(names.get("Func_foo_1"), "Func_foo_1");
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

    #[test]
    fn rewrites_only_qualified_module_references() {
        let names = allocate(&["Func_foo", "Func_Foo"], &[]);
        assert_eq!(
            names.rewrite_references(
                "Func_foo.func_foo (Func_foo) A.Func_foo.x Func_foo.\nFunc_Foo.func_Foo",
                &HashSet::new()
            ),
            "Func_foo_1.func_foo (Func_foo) A.Func_foo.x Func_foo.\nFunc_Foo.func_Foo"
        );
        assert_eq!(
            names.rewrite_references("Func_foo.x", &HashSet::from(["Func_foo"])),
            "Func_foo.x"
        );
    }
}
