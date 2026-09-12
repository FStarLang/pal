//! Model the C builtins PAL understands.
//!
//! `__builtin_unreachable()` is a claim that control never reaches this point.
//! It is how a `noreturn` abort is spelled to the C compiler, and code that
//! ends a switch's default arm with one relies on it: without it the compiler
//! reports the fall-through as a use of an uninitialized variable.
//!
//! Pulse spells the same claim `unreachable ()`, which PAL already emits for
//! `_assert(false)`, so the builtin is rewritten to exactly that. The claim is
//! discharged, not assumed: an arm PAL cannot show is dead is an error.

use std::rc::Rc;

use crate::ir::*;

const UNREACHABLE: &str = "__builtin_unreachable";

fn is_unreachable_call(stmt: &Stmt) -> bool {
    let StmtT::Call(expr) = &stmt.val else {
        return false;
    };
    let ExprT::FnCall(name, args) = &expr.val else {
        return false;
    };
    &*name.val == UNREACHABLE && args.is_empty()
}

fn rewrite_stmts(stmts: &mut Stmts) {
    for stmt in stmts.iter_mut() {
        rewrite_stmt(stmt);
    }
}

fn rewrite_shared_stmts(stmts: &mut Rc<Stmts>) {
    rewrite_stmts(Rc::make_mut(stmts));
}

fn rewrite_stmt(stmt: &mut Rc<Stmt>) {
    if is_unreachable_call(stmt) {
        let loc = stmt.loc.clone();
        let f = Rc::new(Ast {
            val: ExprT::BoolLit(false),
            loc: loc.clone(),
        });
        *stmt = Rc::new(Ast {
            val: StmtT::Assert(f),
            loc,
        });
        return;
    }
    match &mut Rc::make_mut(stmt).val {
        StmtT::If {
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_shared_stmts(then_branch);
            rewrite_shared_stmts(else_branch);
        }
        StmtT::Match {
            branches,
            default_branch,
            ..
        } => {
            for branch in Rc::make_mut(branches).iter_mut() {
                rewrite_shared_stmts(&mut Rc::make_mut(branch).body);
            }
            rewrite_shared_stmts(default_branch);
        }
        StmtT::While { body, .. } => rewrite_shared_stmts(body),
        StmtT::GotoBlock { body, .. } => rewrite_shared_stmts(body),
        _ => {}
    }
}

pub fn builtins(tu: &mut TranslationUnit) {
    for decl in tu.decls.iter_mut() {
        if let DeclT::FnDefn(FnDefn { body, .. }) = &mut decl.val {
            rewrite_stmts(body);
        }
    }
}
