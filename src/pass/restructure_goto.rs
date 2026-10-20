use std::rc::Rc;

use crate::diag::{Diagnostic, DiagnosticLevel, Diagnostics};
use crate::ir::*;

fn stmt_contains_goto(stmt: &Stmt, label: &str) -> bool {
    match &stmt.val {
        StmtT::Goto(l) => *l.val == *label,
        StmtT::If {
            then_branch,
            else_branch,
            ..
        } => stmts_contain_goto(then_branch, label) || stmts_contain_goto(else_branch, label),
        StmtT::While { body, .. } => stmts_contain_goto(body, label),
        StmtT::GotoBlock { body, .. } => stmts_contain_goto(body, label),
        _ => false,
    }
}

fn stmts_contain_goto(stmts: &[Rc<Stmt>], label: &str) -> bool {
    stmts.iter().any(|s| stmt_contains_goto(s, label))
}

fn restructure_stmts(stmts: &mut Vec<Rc<Stmt>>) {
    // First, recursively restructure nested statement lists
    for stmt in stmts.iter_mut() {
        restructure_stmt(Rc::make_mut(stmt));
    }

    // Find and restructure label statements one at a time (from the end).
    // We re-scan after each splice because indices shift.
    let mut skip_labels: Vec<Rc<str>> = Vec::new();
    loop {
        // Find the last label in the current stmts that we haven't skipped
        let label_info = stmts
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, s)| match &s.val {
                StmtT::Label { name, ensures } if !skip_labels.iter().any(|l| **l == *name.val) => {
                    Some((i, name.clone(), ensures.clone()))
                }
                _ => None,
            });

        let Some((label_idx, label_name, label_ensures)) = label_info else {
            break;
        };

        // Find the earliest statement containing a goto to this label
        let first_goto = stmts[..label_idx]
            .iter()
            .position(|s| stmt_contains_goto(s, &label_name.val));

        if let Some(start) = first_goto {
            // Extract statements [start..label_idx) into the block body
            let mut body: Vec<Rc<Stmt>> = stmts[start..label_idx].to_vec();
            // Any label earlier than this one is now nested inside the block we
            // are about to build, so the re-scan below can no longer reach it.
            // Restructure the body as a list to catch those. This terminates
            // because the body excludes `label_idx` and so is strictly shorter
            // than `stmts`.
            restructure_stmts(&mut body);
            let loc = stmts[label_idx].loc.clone();

            let goto_block = StmtT::GotoBlock {
                body: Rc::new(body),
                label: label_name,
                ensures: label_ensures,
            }
            .with_loc(loc);

            // Replace [start..=label_idx] with the single GotoBlock
            stmts.splice(start..=label_idx, std::iter::once(goto_block));
        } else {
            // No goto found for this label — skip it
            skip_labels.push(label_name.val.clone());
        }
    }
}

fn restructure_stmt(stmt: &mut Stmt) {
    match &mut stmt.val {
        StmtT::If {
            then_branch,
            else_branch,
            ..
        } => {
            restructure_stmts(Rc::make_mut(then_branch));
            restructure_stmts(Rc::make_mut(else_branch));
        }
        StmtT::While { body, .. } => {
            restructure_stmts(Rc::make_mut(body));
        }
        StmtT::GotoBlock { body, .. } => {
            restructure_stmts(Rc::make_mut(body));
        }
        _ => {}
    }
}

/// Report every `goto` that restructuring could not turn into a block exit.
///
/// A `goto L` is only expressible in Pulse when it exits the *innermost*
/// enclosing `label` block, and that block is `L`. `if`/`while` are not block
/// exits, so they do not change the innermost label: jumping to the enclosing
/// label from inside a branch or a loop body is the ordinary, working case.
///
/// Anything else is rejected here rather than emitted, because `emit` drops an
/// unrestructured label but still emits its `goto`, which would otherwise
/// produce F* code referring to a label that was never defined.
fn check_gotos_stmt(diags: &mut Diagnostics, stmt: &Stmt, innermost: Option<&str>) {
    match &stmt.val {
        StmtT::Goto(label) => {
            if innermost != Some(&*label.val) {
                diags.report(Diagnostic {
                    loc: stmt.loc.location().clone(),
                    level: DiagnosticLevel::Error,
                    msg: format!(
                        "unsupported goto to `{}`: only a jump to the closest \
                         following label of the enclosing block is supported",
                        label.val
                    ),
                });
            }
        }
        StmtT::If {
            then_branch,
            else_branch,
            ..
        } => {
            check_gotos_stmts(diags, then_branch, innermost);
            check_gotos_stmts(diags, else_branch, innermost);
        }
        StmtT::While { body, .. } => check_gotos_stmts(diags, body, innermost),
        StmtT::GotoBlock { body, label, .. } => {
            check_gotos_stmts(diags, body, Some(&label.val));
        }
        _ => {}
    }
}

fn check_gotos_stmts(diags: &mut Diagnostics, stmts: &[Rc<Stmt>], innermost: Option<&str>) {
    for stmt in stmts {
        check_gotos_stmt(diags, stmt, innermost);
    }
}

fn restructure_decl(decl: &mut Decl) {
    match &mut decl.val {
        DeclT::FnDefn(FnDefn { body, .. }) => {
            restructure_stmts(body);
        }
        _ => {}
    }
}

pub fn restructure_goto(diags: &mut Diagnostics, tu: &mut TranslationUnit) {
    for decl in &mut tu.decls {
        restructure_decl(decl);
        if let DeclT::FnDefn(FnDefn { body, .. }) = &decl.val {
            check_gotos_stmts(diags, body, None);
        }
    }
}
