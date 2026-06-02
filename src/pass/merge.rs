use std::collections::HashMap;
use std::rc::Rc;

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    env::Env,
    ir::*,
};

fn report(diags: &mut Diagnostics, msg: String, loc: &SourceInfo) {
    diags.report(Diagnostic {
        loc: loc.location().clone(),
        level: DiagnosticLevel::Error,
        msg,
    });
}

fn types_match(env: &Env, decl: &FnDecl, defn: &FnDecl) -> bool {
    if decl.args.len() != defn.args.len() {
        return false;
    }
    for (arg_a, arg_b) in decl.args.iter().zip(defn.args.iter()) {
        if !env.vtype_eq(arg_a.ty.clone().into(), arg_b.ty.clone().into()) {
            return false;
        }
    }
    env.vtype_eq(decl.ret_type.clone().into(), defn.ret_type.clone().into())
}

pub fn merge(diags: &mut Diagnostics, tu: &mut TranslationUnit) {
    // === Phase 1: Deduplicate identical declarations from shared headers ===
    // For each declaration kind+name, keep the most complete (last) content at the
    // earliest (first) position. This preserves the source ordering so that later
    // passes (e.g. elab) that build their environment incrementally see types
    // before they are referenced by `_include_pulse` blocks in the same file.
    {
        let mut first_idx: HashMap<(u8, Rc<str>), usize> = HashMap::new();
        let mut moves: Vec<(usize, usize)> = Vec::new();
        let mut to_remove: Vec<usize> = Vec::new();

        for (i, decl) in tu.decls.iter().enumerate() {
            // Classify by a (kind_tag, name) key
            let key: Option<(u8, Rc<str>)> = match &decl.val {
                DeclT::Typedef(td) => Some((0, td.name.val.clone())),
                DeclT::StructDefn(sd) => Some((1, sd.name.val.clone())),
                DeclT::StructDecl(name) => Some((2, name.val.clone())),
                DeclT::UnionDefn(ud) => Some((3, ud.name.val.clone())),
                DeclT::FnDefn(fd) => Some((4, fd.decl.name.val.clone())),
                DeclT::FnDecl(fd) => Some((5, fd.name.val.clone())),
                DeclT::GlobalVar(gv) => Some((6, gv.name.val.clone())),
                DeclT::IncludeDecl(inc) => Some((7, inc.module_name.clone())),
                DeclT::LetDecl(ld) => Some((8, ld.name.val.clone())),
                DeclT::OpaqueTypeDecl(td) => Some((9, td.name.val.clone())),
            };
            if let Some(key) = key {
                if let Some(&first) = first_idx.get(&key) {
                    // Copy this (later, more complete) decl back to the first position
                    // and mark this duplicate for removal.
                    moves.push((i, first));
                    to_remove.push(i);
                } else {
                    first_idx.insert(key, i);
                }
            }
        }

        // Apply moves in order so the final value at each first position is the
        // last (most complete) occurrence.
        for &(src, dst) in &moves {
            tu.decls[dst] = tu.decls[src].clone();
        }

        to_remove.sort_unstable();
        to_remove.dedup();
        for &i in to_remove.iter().rev() {
            tu.decls.remove(i);
        }
    }

    // === Phase 2: Merge FnDecl specs into FnDefn, remove redundant StructDecls ===
    // Build index: fn name → position of its FnDefn in tu.decls.
    // Also index StructDefns and UnionDefns by name so we can move them to the
    // position of the earliest StructDecl/declaration that referenced them.
    let mut defn_indices: HashMap<Rc<str>, usize> = HashMap::new();
    let mut struct_defn_indices: HashMap<Rc<str>, usize> = HashMap::new();
    for (i, decl) in tu.decls.iter().enumerate() {
        match &decl.val {
            DeclT::FnDefn(fn_defn) => {
                defn_indices.insert(fn_defn.decl.name.val.clone(), i);
            }
            DeclT::StructDefn(struct_defn) => {
                struct_defn_indices.insert(struct_defn.name.val.clone(), i);
            }
            _ => {}
        }
    }

    // Track which indices to remove (merged into their FnDefn/StructDefn).
    let mut to_remove: Vec<usize> = Vec::new();
    // Track moves: copy content from src to dst (applied after the analysis loop).
    let mut moves: Vec<(usize, usize)> = Vec::new();

    // Build an Env for type comparison (need typedef resolution)
    let mut env = Env::new();
    for decl in tu.decls.iter() {
        env.push_decl(decl);
    }

    // Match each FnDecl to its FnDefn
    for (i, decl) in tu.decls.iter().enumerate() {
        match &decl.val {
            DeclT::FnDecl(fn_decl) => {
                if let Some(&defn_idx) = defn_indices.get(&fn_decl.name.val) {
                    let defn = match &tu.decls[defn_idx].val {
                        DeclT::FnDefn(fd) => fd,
                        _ => unreachable!(),
                    };

                    // Validate types match
                    if !types_match(&env, fn_decl, &defn.decl) {
                        report(
                            diags,
                            format!(
                                "declaration of {} has different types than its definition",
                                fn_decl.name.val
                            ),
                            &fn_decl.name.loc,
                        );
                        continue;
                    }

                    let decl_has_specs =
                        !fn_decl.requires.is_empty() || !fn_decl.ensures.is_empty();
                    let defn_has_specs =
                        !defn.decl.requires.is_empty() || !defn.decl.ensures.is_empty();

                    if defn_has_specs && !decl_has_specs {
                        // Specs on the definition but not on the declaration — error
                        report(
                            diags,
                            format!(
                                "definition of {} has specifications, but its declaration does not; \
                             specifications should be on the declaration",
                                fn_decl.name.val
                            ),
                            &defn.decl.name.loc,
                        );
                        continue;
                    }

                    if decl_has_specs && defn_has_specs {
                        // Both have specs — they must match
                        if fn_decl.requires != defn.decl.requires
                            || fn_decl.ensures != defn.decl.ensures
                        {
                            report(
                                diags,
                                format!(
                                    "declaration and definition of {} have differing specifications",
                                    fn_decl.name.val
                                ),
                                &fn_decl.name.loc,
                            );
                            continue;
                        }
                    }

                    // Mark FnDecl for removal — it will be merged into the FnDefn.
                    // If the forward declaration came before the definition, move
                    // the (spec-merged) definition back to the declaration's
                    // position so that other declarations between the two (e.g.
                    // _include_pulse blocks, callers) can still resolve it.
                    if i < defn_idx {
                        moves.push((defn_idx, i));
                        to_remove.push(defn_idx);
                    } else {
                        to_remove.push(i);
                    }
                }
            }
            // Remove StructDecl when a matching StructDefn exists. As with
            // functions, hoist the StructDefn to the earliest StructDecl
            // position when the decl comes first.
            DeclT::StructDecl(name) => {
                if let Some(&defn_idx) = struct_defn_indices.get(&name.val) {
                    if i < defn_idx {
                        moves.push((defn_idx, i));
                        to_remove.push(defn_idx);
                    } else {
                        to_remove.push(i);
                    }
                }
            }
            _ => {}
        }
    }

    // Copy specs from declarations into definitions before removing them
    // (need a separate pass to avoid borrow conflicts)
    for &i in &to_remove {
        let DeclT::FnDecl(fn_decl) = &tu.decls[i].val else {
            continue;
        };
        let fn_decl = fn_decl.clone();
        if let Some(&defn_idx) = defn_indices.get(&fn_decl.name.val) {
            if let DeclT::FnDefn(ref mut defn) = tu.decls[defn_idx].val {
                if defn.decl.requires.is_empty() && defn.decl.ensures.is_empty() {
                    defn.decl.requires = fn_decl.requires;
                    defn.decl.ensures = fn_decl.ensures;
                }
            }
        }
    }

    // Apply moves: copy the spec-merged FnDefn/StructDefn into the position
    // of its earliest forward declaration.
    for &(src, dst) in &moves {
        tu.decls[dst] = tu.decls[src].clone();
    }

    // Remove merged decls (iterate in reverse to preserve indices)
    to_remove.sort_unstable();
    to_remove.dedup();
    for &i in to_remove.iter().rev() {
        tu.decls.remove(i);
    }
}
