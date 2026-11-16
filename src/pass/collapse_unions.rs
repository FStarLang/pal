//! Collapse an `_overlay` union whose members are all one integer type into
//! that type.
//!
//! Such a union is how C renames a field without breaking old readers
//! (`union { id_t DriveId; id_t DiskNumber; }`): every member is the same
//! bytes read the same way, so it is the integer, and any member may be read
//! whatever member was written. Modelled as an overlay, a read would need the
//! member's bytes to be known readable -- a fact no caller states, since in C
//! there is nothing to state. A union that is not `_overlay` is left alone: its
//! active member is a tag, which a specification may use. After this pass `e.m` is `e`, `(U){.m = v}` is
//! `v`, `e.m._active` is `true`, and `U` is the integer type everywhere.

use std::collections::HashMap;
use std::rc::Rc;

use crate::{
    env::{Env, LocalDeclKind},
    ir::*,
};

type Collapsed = HashMap<Rc<str>, Rc<Type>>;

fn collapsible(env: &Env, u: &UnionDefn) -> Option<Rc<Type>> {
    if !u.overlay || u.fields.len() < 2 || !u.owning.is_empty() {
        return None;
    }
    let mut tys = Vec::new();
    for f in &u.fields {
        let FieldT::Plain { ty, .. } = &f.val else {
            return None;
        };
        tys.push(ty.clone());
    }
    let first = tys[0].clone();
    // `vtype_eq` sees through a refinement, which would either lose a
    // member's or impose it on the others: such a union stays an overlay.
    if !tys.iter().all(|t| bare_int(env, t)) {
        return None;
    }
    tys.iter()
        .all(|t| env.vtype_eq(t.clone().into(), first.clone().into()))
        .then_some(first)
}

/// Whether `t` is an integer type, through typedefs but not refinements.
fn bare_int(env: &Env, t: &Type) -> bool {
    match &t.val {
        TypeT::Int { .. } => true,
        TypeT::TypeRef(TypeRefKind::Typedef(n)) => {
            env.lookup_type(n).is_some_and(|d| bare_int(env, &d.body))
        }
        _ => false,
    }
}

fn collapsed_of<'a>(env: &Env, c: &'a Collapsed, e: &Expr) -> Option<&'a Rc<Type>> {
    let ty = env.infer_expr(e).ok()?;
    match &env.vtype_whnf(ty).val {
        TypeT::TypeRef(TypeRefKind::Union(n)) => c.get(&*n.val),
        _ => None,
    }
}

fn ty(env: &Env, c: &Collapsed, t: &mut Rc<Type>) {
    if let TypeT::TypeRef(TypeRefKind::Union(n)) = &t.val
        && let Some(r) = c.get(&*n.val)
    {
        *t = r.clone();
        return;
    }
    // A refinement's `this` has the type before collapsing, so that the
    // predicate's own members are recognised.
    let orig = t.clone();
    match &mut Rc::make_mut(t).val {
        TypeT::Pointer(inner, _)
        | TypeT::FixedArray(inner, _)
        | TypeT::FlexArray(inner)
        | TypeT::Plain(inner)
        | TypeT::Nullable(inner)
        | TypeT::Overread(inner) => ty(env, c, inner),
        TypeT::FnPtr { args, ret } => {
            for a in args {
                ty(env, c, a);
            }
            ty(env, c, ret);
        }
        TypeT::Refine(inner, pred)
        | TypeT::RefineAlways(inner, pred)
        | TypeT::RefineUninit(inner, pred) => {
            let mut e = env.clone();
            if let TypeT::Refine(i, _) | TypeT::RefineAlways(i, _) | TypeT::RefineUninit(i, _) =
                &orig.val
            {
                e.push_this(i.clone());
            }
            expr(&e, c, Rc::make_mut(pred));
            ty(env, c, inner);
        }
        TypeT::RefineValue(inner, _, binding_ty, pred) => {
            let mut e = env.clone();
            if let TypeT::RefineValue(i, _, _, _) = &orig.val {
                e.push_this(i.clone());
            }
            expr(&e, c, Rc::make_mut(pred));
            ty(env, c, inner);
            ty(env, c, binding_ty);
        }
        TypeT::Void
        | TypeT::Bool
        | TypeT::Int { .. }
        | TypeT::Float { .. }
        | TypeT::SizeT
        | TypeT::PtrdiffT
        | TypeT::SpecInt
        | TypeT::SpecNat
        | TypeT::SLProp
        | TypeT::TypeRef(_)
        | TypeT::Unknown
        | TypeT::Error => {}
    }
}

fn inline_pulse(env: &Env, c: &Collapsed, code: &mut InlinePulseCode) {
    for token in &mut code.tokens {
        match token {
            InlinePulseToken::RValueAntiquot { expr: e, .. }
            | InlinePulseToken::LValueAntiquot { expr: e, .. } => expr(env, c, Rc::make_mut(e)),
            InlinePulseToken::TypeAntiquot { ty: t, .. }
            | InlinePulseToken::FieldAntiquot { ty: t, .. }
            | InlinePulseToken::AuxFnAntiquot { ty: t, .. }
            | InlinePulseToken::Declare { ty: t, .. } => ty(env, c, t),
            InlinePulseToken::Verbatim(_) | InlinePulseToken::WitnessAntiquot(_) => {}
        }
    }
}

fn exprs(env: &Env, c: &Collapsed, es: &mut Exprs) {
    for e in es {
        expr(env, c, Rc::make_mut(e));
    }
}

fn expr(env: &Env, c: &Collapsed, e: &mut Expr) {
    // Decided on the expression as written, whose types the environment has.
    match &e.val {
        ExprT::Member(base, _) if collapsed_of(env, c, base).is_some() => {
            let mut b = (**base).clone();
            expr(env, c, &mut b);
            e.val = b.val;
            return;
        }
        ExprT::VAttr(VAttr::Active(_), base) if collapsed_of(env, c, base).is_some() => {
            e.val = ExprT::BoolLit(true);
            return;
        }
        ExprT::UnionInit(n, _, v) if c.contains_key(&*n.val) => {
            let mut v = (**v).clone();
            expr(env, c, &mut v);
            e.val = v.val;
            return;
        }
        _ => {}
    }
    match &mut e.val {
        ExprT::IntLit(_, t)
        | ExprT::FloatLit(_, t)
        | ExprT::Malloc(t)
        | ExprT::Calloc(t)
        | ExprT::SizeOf(t)
        | ExprT::AlignOf(t)
        | ExprT::Error(t) => ty(env, c, t),
        ExprT::InlinePulse(code, t) => {
            inline_pulse(env, c, Rc::make_mut(code));
            ty(env, c, t);
        }
        ExprT::Cast(v, t)
        | ExprT::MallocArray(t, v)
        | ExprT::CallocArray(t, v)
        | ExprT::MallocFlex(t, v)
        | ExprT::CallocFlex(t, v)
        | ExprT::MemsetZero(t, v)
        | ExprT::ContainerOf(v, t, _) => {
            expr(env, c, Rc::make_mut(v));
            ty(env, c, t);
        }
        ExprT::Forall(x, t, body) | ExprT::Exists(x, t, body) => {
            let mut inner = env.clone();
            inner.push_var_decl(x, t.clone(), LocalDeclKind::RValue);
            expr(&inner, c, Rc::make_mut(body));
            ty(env, c, t);
        }
        ExprT::ArrayInit { elem_ty, elems, .. } => {
            ty(env, c, elem_ty);
            exprs(env, c, elems);
        }
        ExprT::Memset(t, d, v, n) => {
            ty(env, c, t);
            expr(env, c, Rc::make_mut(d));
            expr(env, c, Rc::make_mut(v));
            expr(env, c, Rc::make_mut(n));
        }
        ExprT::Deref(v)
        | ExprT::Member(v, _)
        | ExprT::VAttr(_, v)
        | ExprT::Ref(v)
        | ExprT::UnOp(_, v)
        | ExprT::Live(v)
        | ExprT::Unchanged(v)
        | ExprT::Old(v)
        | ExprT::Free(v)
        | ExprT::PreIncr(v)
        | ExprT::PostIncr(v)
        | ExprT::PreDecr(v)
        | ExprT::PostDecr(v)
        | ExprT::UnionInit(_, _, v) => expr(env, c, Rc::make_mut(v)),
        ExprT::Index(l, r) | ExprT::BinOp(_, l, r) | ExprT::AssignExpr(l, r) => {
            expr(env, c, Rc::make_mut(l));
            expr(env, c, Rc::make_mut(r));
        }
        ExprT::Cond(a, b, d) => {
            expr(env, c, Rc::make_mut(a));
            expr(env, c, Rc::make_mut(b));
            expr(env, c, Rc::make_mut(d));
        }
        ExprT::FnCall(_, args) => exprs(env, c, args),
        ExprT::FnPtrCall(f, args) => {
            expr(env, c, Rc::make_mut(f));
            exprs(env, c, args);
        }
        ExprT::StructInit(_, fields) => {
            for (_, v) in fields {
                expr(env, c, Rc::make_mut(v));
            }
        }
        ExprT::Var(_) | ExprT::FnRef(_) | ExprT::BoolLit(_) => {}
    }
}

fn stmt(env: &mut Env, c: &Collapsed, s: &mut Stmt) {
    // The declaration enters scope with its type as written, before that is
    // collapsed, so later uses of the variable are recognised.
    env.push_stmt(s);
    match &mut s.val {
        StmtT::Call(e) | StmtT::Assert(e) | StmtT::Return(Some(e)) => expr(env, c, Rc::make_mut(e)),
        StmtT::Decl(_, t) => ty(env, c, t),
        StmtT::Let(_, t, v) => {
            ty(env, c, t);
            expr(env, c, Rc::make_mut(v));
        }
        StmtT::DeclStackArray {
            elem_type, size, ..
        } => {
            ty(env, c, elem_type);
            expr(env, c, Rc::make_mut(size));
        }
        StmtT::Assign(l, r) => {
            expr(env, c, Rc::make_mut(l));
            expr(env, c, Rc::make_mut(r));
        }
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ensures,
        } => {
            expr(env, c, Rc::make_mut(cond));
            stmts(env, c, Rc::make_mut(then_branch));
            stmts(env, c, Rc::make_mut(else_branch));
            exprs(env, c, Rc::make_mut(ensures));
        }
        StmtT::Match {
            scrutinee,
            branches,
            default_branch,
            ensures,
        } => {
            expr(env, c, Rc::make_mut(scrutinee));
            for b in Rc::make_mut(branches) {
                let b = Rc::make_mut(b);
                exprs(env, c, Rc::make_mut(&mut b.patterns));
                stmts(env, c, Rc::make_mut(&mut b.body));
            }
            stmts(env, c, Rc::make_mut(default_branch));
            exprs(env, c, Rc::make_mut(ensures));
        }
        StmtT::While {
            cond,
            inv,
            requires,
            ensures,
            body,
        } => {
            expr(env, c, Rc::make_mut(cond));
            exprs(env, c, Rc::make_mut(inv));
            exprs(env, c, Rc::make_mut(requires));
            exprs(env, c, Rc::make_mut(ensures));
            stmts(env, c, Rc::make_mut(body));
        }
        StmtT::GhostStmt(code) => inline_pulse(env, c, Rc::make_mut(code)),
        StmtT::Label { ensures, .. } => exprs(env, c, Rc::make_mut(ensures)),
        StmtT::GotoBlock { body, ensures, .. } => {
            stmts(env, c, Rc::make_mut(body));
            exprs(env, c, Rc::make_mut(ensures));
        }
        StmtT::Break | StmtT::Continue | StmtT::Return(None) | StmtT::Goto(_) | StmtT::Error => {}
    }
}

fn stmts(env: &Env, c: &Collapsed, ss: &mut Stmts) {
    let mut env = env.clone();
    for s in ss {
        stmt(&mut env, c, Rc::make_mut(s));
    }
}

fn fn_decl(env: &Env, c: &Collapsed, d: &mut FnDecl) {
    let mut spec = env.clone();
    spec.push_fn_decl_args_for_body(d);
    let pre = spec.clone();
    spec.push_return(d.ret_type.clone());
    exprs(&pre, c, &mut d.requires);
    exprs(&spec, c, &mut d.ensures);
    if let Some(dec) = &mut d.decreases {
        expr(&pre, c, Rc::make_mut(dec));
    }
    ty(env, c, &mut d.ret_type);
    for a in &mut d.args {
        ty(env, c, &mut a.ty);
    }
    for a in &mut d.ghost_args {
        ty(env, c, &mut a.ty);
    }
}

fn fields(env: &Env, c: &Collapsed, fs: &mut [Field]) {
    for f in fs {
        match &mut f.val {
            FieldT::Plain { ty: t, .. } | FieldT::BitField { ty: t, .. } => ty(env, c, t),
        }
    }
}

fn decl(env: &Env, c: &Collapsed, d: &mut Decl) {
    match &mut d.val {
        DeclT::FnDefn(def) => {
            let mut body = env.clone();
            body.push_fn_decl_args_for_body(&def.decl);
            body.set_return_type(def.decl.ret_type.clone());
            stmts(&body, c, &mut def.body);
            fn_decl(env, c, &mut def.decl);
        }
        DeclT::FnDecl(fd) => fn_decl(env, c, fd),
        DeclT::Typedef(def) => ty(env, c, &mut def.body),
        DeclT::StructDefn(def) => {
            ty(env, c, &mut def.refines);
            fields(env, c, &mut def.fields);
        }
        DeclT::UnionDefn(def) => fields(env, c, &mut def.fields),
        DeclT::IncludeDecl(inc) => inline_pulse(env, c, &mut inc.code),
        DeclT::LetDecl(ld) => {
            let mut e = env.clone();
            for p in &ld.params {
                if let Some(n) = &p.name {
                    e.push_var_decl(n, p.ty.clone(), LocalDeclKind::RValue);
                }
            }
            exprs(&e, c, &mut ld.requires);
            exprs(&e, c, &mut ld.ensures);
            expr(&e, c, Rc::make_mut(&mut ld.body));
            ty(env, c, &mut ld.ret_type);
            for p in &mut ld.params {
                ty(env, c, &mut p.ty);
            }
        }
        DeclT::OpaqueTypeDecl(od) => inline_pulse(env, c, &mut od.code),
        DeclT::GlobalVar(g) => {
            if let Some(init) = &mut g.init {
                expr(env, c, Rc::make_mut(init));
            }
            ty(env, c, &mut g.ty);
        }
        DeclT::StructDecl(_) => {}
    }
}

pub fn collapse_unions(tu: &mut TranslationUnit) {
    let mut env = Env::new();
    for d in &tu.decls {
        env.push_decl(d);
    }
    let c: Collapsed = tu
        .decls
        .iter()
        .filter_map(|d| match &d.val {
            DeclT::UnionDefn(u) => collapsible(&env, u).map(|t| (u.name.val.clone(), t)),
            _ => None,
        })
        .collect();
    if c.is_empty() {
        return;
    }
    // The union definitions go: nothing refers to them any more.
    for d in &mut tu.decls {
        decl(&env, &c, d);
    }
    tu.decls
        .retain(|d| !matches!(&d.val, DeclT::UnionDefn(u) if c.contains_key(&*u.name.val)));
}
