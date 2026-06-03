//! Decay pass: rewrites FixedArray types in function parameters to Pointer(T, Array).
//!
//! In C, array parameters decay to pointers. Clang typically adjusts parameter types,
//! but this pass ensures any remaining FixedArray in parameter positions is decayed.

use std::rc::Rc;

use crate::ir::*;

fn decay_type(ty: &Rc<Type>) -> Rc<Type> {
    match &ty.val {
        TypeT::FixedArray(elem, _) => {
            TypeT::Pointer(elem.clone(), PointerKind::Array).with_loc(ty.loc.clone())
        }
        _ => ty.clone(),
    }
}

fn decay_fn_decl(decl: &mut FnDecl) {
    for arg in decl.args.iter_mut() {
        arg.ty = decay_type(&arg.ty);
    }
    for ga in decl.ghost_args.iter_mut() {
        ga.ty = decay_type(&ga.ty);
    }
}

pub fn decay(tu: &mut TranslationUnit) {
    for decl in &mut tu.decls {
        match &mut decl.val {
            DeclT::FnDefn(defn) => {
                decay_fn_decl(&mut defn.decl);
            }
            DeclT::FnDecl(fd) => {
                decay_fn_decl(fd);
            }
            _ => {}
        }
    }
}
