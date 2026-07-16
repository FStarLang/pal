//! `elim_simple_cis` pass: eliminates a union that is a *simple Common Initial
//! Sequence* (CIS) shape, collapsing it into a plain struct.
//!
//! Runs **after elaboration** so that `env.infer_expr` / `env.lookup_union` are
//! available (mirroring `elab.rs`). A union qualifies iff:
//!   1. it has exactly two arms,
//!   2. one arm is anonymous (synthesized name `_unnamed…`) and the other is a
//!      named struct field, and
//!   3. both arms are struct-typed with identical field lists (same length,
//!      same field names, same types).
//!
//! For a qualifying union the pass rewrites, across the whole translation unit:
//!   - `Member(base, arm)` where `base` has the eliminated union type and `arm`
//!     is one of its arm names  ->  `base` (collapses both `u->n.p1` and the
//!     promoted `u->p1` down to `u.p1`);
//!   - `UnionInit(u, arm, StructInit(_, kvs))`  ->  `StructInit(u, kvs)`;
//!   - the `UnionDefn` itself  ->  a `StructDefn` holding the shared CIS fields;
//!   - every `TypeRef(Union(u))`  ->  `TypeRef(Struct(u))`.
//!
//! Downstream `emit` then produces an ordinary single-constructor struct record
//! (no branches), reusing all existing struct machinery. Unions that do not
//! match the strict shape are left completely untouched.

use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{diag::Diagnostics, env::Env, ir::*, mayberc::MaybeRc};

/// Per-eliminated-union information.
struct ElimUnion {
    /// The two arm (field) names of the union.
    arm_names: Vec<Rc<IdentT>>,
    /// The shared CIS fields that become the fields of the replacement struct.
    cis_fields: Vec<Field>,
}

/// If `f` is a plain field whose type resolves to a struct, return that struct's
/// field list.
fn arm_struct_fields(env: &Env, f: &Field) -> Option<Vec<Field>> {
    if f.val.bit_width().is_some() {
        return None;
    }
    let ty: MaybeRc<Type> = f.val.logical_type(&f.loc).into();
    let ty = env.vtype_whnf(ty);
    match &ty.val {
        TypeT::TypeRef(TypeRefKind::Struct(sname)) => {
            let s = env.lookup_struct(sname)?;
            Some(s.fields.clone())
        }
        _ => None,
    }
}

/// Structural type equality ignoring source locations.
fn type_alpha_eq(a: &Type, b: &Type) -> bool {
    use TypeT::*;
    match (&a.val, &b.val) {
        (Void, Void)
        | (Bool, Bool)
        | (SizeT, SizeT)
        | (PtrdiffT, PtrdiffT)
        | (SpecInt, SpecInt)
        | (SpecNat, SpecNat)
        | (SLProp, SLProp) => true,
        (
            Int {
                signed: s1,
                width: w1,
            },
            Int {
                signed: s2,
                width: w2,
            },
        ) => s1 == s2 && w1 == w2,
        (Float { width: w1 }, Float { width: w2 }) => w1 == w2,
        (Pointer(a1, k1), Pointer(b1, k2)) => k1 == k2 && type_alpha_eq(a1, b1),
        (FixedArray(a1, n1), FixedArray(b1, n2)) => n1 == n2 && type_alpha_eq(a1, b1),
        (TypeRef(k1), TypeRef(k2)) => k1.alpha_eq(k2),
        (Nullable(a1), Nullable(b1)) => type_alpha_eq(a1, b1),
        (Plain(a1), Plain(b1)) => type_alpha_eq(a1, b1),
        _ => false,
    }
}

/// Detect whether `u` is a simple-CIS union; if so return the shared CIS field
/// list to use for the replacement struct.
fn is_simple_cis(env: &Env, u: &UnionDefn) -> Option<Vec<Field>> {
    // Condition 1: exactly two arms.
    if u.fields.len() != 2 {
        return None;
    }
    let arm0 = &u.fields[0];
    let arm1 = &u.fields[1];
    let is_anon = |f: &Field| f.val.name().val.starts_with("_unnamed");
    // Condition 2: exactly one anonymous arm and one named arm.
    if is_anon(arm0) == is_anon(arm1) {
        return None;
    }
    // Both arms must be struct-typed.
    let s0 = arm_struct_fields(env, arm0)?;
    let s1 = arm_struct_fields(env, arm1)?;
    // Condition 3: identical field lists (same length, names and types).
    if s0.len() != s1.len() {
        return None;
    }
    for (f0, f1) in s0.iter().zip(s1.iter()) {
        if f0.val.name().val != f1.val.name().val {
            return None;
        }
        if f0.val.bit_width() != f1.val.bit_width() {
            return None;
        }
        if !type_alpha_eq(&f0.val.logical_type(&f0.loc), &f1.val.logical_type(&f1.loc)) {
            return None;
        }
    }
    Some(s0)
}

pub fn elim_simple_cis(_diags: &mut Diagnostics, tu: &mut TranslationUnit) {
    // Snapshot environment with every declaration (unions still unions), so
    // `infer_expr` resolves union member accesses during the rewrite below.
    let mut env = Env::new();
    for decl in tu.decls.iter() {
        env.push_decl(decl);
    }

    // Detect eliminable unions.
    let mut elim: HashMap<Rc<IdentT>, ElimUnion> = HashMap::new();
    for decl in tu.decls.iter() {
        if let DeclT::UnionDefn(u) = &decl.val {
            if let Some(cis_fields) = is_simple_cis(&env, u) {
                let arm_names = u.fields.iter().map(|f| f.val.name().val.clone()).collect();
                elim.insert(
                    u.name.val.clone(),
                    ElimUnion {
                        arm_names,
                        cis_fields,
                    },
                );
            }
        }
    }
    if elim.is_empty() {
        return;
    }
    let elim_names: HashSet<Rc<IdentT>> = elim.keys().cloned().collect();

    // Phase 1: env-threaded expression rewrites (arm-access collapse + union
    // init -> struct init).
    for decl in tu.decls.iter_mut() {
        if let DeclT::FnDefn(FnDefn {
            decl: fn_decl,
            body,
        }) = &mut decl.val
        {
            let env = &mut env.clone();
            env.push_fn_decl_args_for_body(fn_decl);
            for e in fn_decl
                .requires
                .iter_mut()
                .chain(fn_decl.ensures.iter_mut())
            {
                rewrite_expr(env, Rc::make_mut(e), &elim);
            }
            rewrite_stmts(env, body, &elim);
        }
    }

    // Phase 2: rewrite all `Union(u)` type references to `Struct(u)`, then swap
    // each eliminated `UnionDefn` for a `StructDefn` of the shared CIS fields.
    for decl in tu.decls.iter_mut() {
        rewrite_types_decl(&mut decl.val, &elim_names);
    }
    for decl in tu.decls.iter_mut() {
        if let DeclT::UnionDefn(u) = &decl.val {
            if let Some(info) = elim.get(&u.name.val) {
                decl.val = DeclT::StructDefn(StructDefn {
                    name: u.name.clone(),
                    fields: info.cis_fields.clone(),
                    eager_unfold_pred: false,
                });
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 1: expression rewrites
// ---------------------------------------------------------------------------

fn rewrite_stmts(env: &Env, stmts: &mut Stmts, elim: &HashMap<Rc<IdentT>, ElimUnion>) {
    let env = &mut env.clone();
    for stmt in stmts.iter_mut() {
        rewrite_stmt(env, Rc::make_mut(stmt), elim);
        env.push_stmt(stmt);
    }
}

fn rewrite_stmt(env: &Env, stmt: &mut Stmt, elim: &HashMap<Rc<IdentT>, ElimUnion>) {
    match &mut stmt.val {
        StmtT::Call(e) | StmtT::Assert(e) => rewrite_expr(env, Rc::make_mut(e), elim),
        StmtT::DeclStackArray { size, .. } => rewrite_expr(env, Rc::make_mut(size), elim),
        StmtT::Assign(lhs, rhs) => {
            rewrite_expr(env, Rc::make_mut(lhs), elim);
            rewrite_expr(env, Rc::make_mut(rhs), elim);
        }
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ensures,
        } => {
            rewrite_expr(env, Rc::make_mut(cond), elim);
            rewrite_stmts(env, Rc::make_mut(then_branch), elim);
            rewrite_stmts(env, Rc::make_mut(else_branch), elim);
            for e in Rc::make_mut(ensures).iter_mut() {
                rewrite_expr(env, Rc::make_mut(e), elim);
            }
        }
        StmtT::While {
            cond,
            inv,
            requires,
            ensures,
            body,
        } => {
            rewrite_expr(env, Rc::make_mut(cond), elim);
            for e in Rc::make_mut(inv)
                .iter_mut()
                .chain(Rc::make_mut(requires).iter_mut())
                .chain(Rc::make_mut(ensures).iter_mut())
            {
                rewrite_expr(env, Rc::make_mut(e), elim);
            }
            rewrite_stmts(env, Rc::make_mut(body), elim);
        }
        StmtT::Return(Some(e)) => rewrite_expr(env, Rc::make_mut(e), elim),
        StmtT::Label { ensures, .. } => {
            for e in Rc::make_mut(ensures).iter_mut() {
                rewrite_expr(env, Rc::make_mut(e), elim);
            }
        }
        StmtT::GotoBlock { body, ensures, .. } => {
            rewrite_stmts(env, Rc::make_mut(body), elim);
            for e in Rc::make_mut(ensures).iter_mut() {
                rewrite_expr(env, Rc::make_mut(e), elim);
            }
        }
        StmtT::Decl(..)
        | StmtT::Break
        | StmtT::Continue
        | StmtT::Return(None)
        | StmtT::GhostStmt(_)
        | StmtT::Goto(_)
        | StmtT::Error => {}
    }
}

fn rewrite_expr(env: &Env, e: &mut Expr, elim: &HashMap<Rc<IdentT>, ElimUnion>) {
    // Recurse into children first.
    match &mut e.val {
        ExprT::Deref(x)
        | ExprT::Member(x, _)
        | ExprT::VAttr(_, x)
        | ExprT::Ref(x)
        | ExprT::UnOp(_, x)
        | ExprT::Cast(x, _)
        | ExprT::ContainerOf(x, _, _)
        | ExprT::Live(x)
        | ExprT::Old(x)
        | ExprT::Forall(_, _, x)
        | ExprT::Exists(_, _, x)
        | ExprT::PreIncr(x)
        | ExprT::PostIncr(x)
        | ExprT::PreDecr(x)
        | ExprT::PostDecr(x)
        | ExprT::Free(x)
        | ExprT::MemsetZero(_, x)
        | ExprT::MallocArray(_, x)
        | ExprT::CallocArray(_, x)
        | ExprT::UnionInit(_, _, x) => rewrite_expr(env, Rc::make_mut(x), elim),
        ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
            rewrite_expr(env, Rc::make_mut(a), elim);
            rewrite_expr(env, Rc::make_mut(b), elim);
        }
        ExprT::Cond(a, b, c) => {
            rewrite_expr(env, Rc::make_mut(a), elim);
            rewrite_expr(env, Rc::make_mut(b), elim);
            rewrite_expr(env, Rc::make_mut(c), elim);
        }
        ExprT::Memset(_, a, b, c) => {
            rewrite_expr(env, Rc::make_mut(a), elim);
            rewrite_expr(env, Rc::make_mut(b), elim);
            rewrite_expr(env, Rc::make_mut(c), elim);
        }
        ExprT::FnCall(_, args) | ExprT::ArrayInit(_, args) => {
            for a in args.iter_mut() {
                rewrite_expr(env, Rc::make_mut(a), elim);
            }
        }
        ExprT::StructInit(_, kvs) => {
            for (_, v) in kvs.iter_mut() {
                rewrite_expr(env, Rc::make_mut(v), elim);
            }
        }
        ExprT::Var(_)
        | ExprT::BoolLit(_)
        | ExprT::IntLit(_, _)
        | ExprT::FloatLit(_, _)
        | ExprT::InlinePulse(_, _)
        | ExprT::Malloc(_)
        | ExprT::Calloc(_)
        | ExprT::SizeOf(_)
        | ExprT::AlignOf(_)
        | ExprT::Error(_) => {}
    }

    // Rewrite `UnionInit(u, arm, StructInit(_, kvs))` -> `StructInit(u, kvs)`.
    let uinit = if let ExprT::UnionInit(uname, _arm, val) = &e.val {
        if elim.contains_key(&uname.val) {
            if let ExprT::StructInit(_sname, kvs) = &val.val {
                Some((uname.clone(), kvs.clone()))
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };
    if let Some((uname, kvs)) = uinit {
        e.val = ExprT::StructInit(uname, kvs);
        return;
    }

    // Collapse `Member(base, arm)` -> `base` when `base` is an eliminated-union
    // type and `arm` is one of its arm names.
    let collapse = if let ExprT::Member(base, arm) = &e.val {
        match env.infer_expr(base) {
            Ok(t) => {
                let t = env.vtype_whnf(t);
                if let TypeT::TypeRef(TypeRefKind::Union(uname)) = &t.val {
                    match elim.get(&uname.val) {
                        Some(info) if info.arm_names.contains(&arm.val) => Some(base.clone()),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            Err(_) => None,
        }
    } else {
        None
    };
    if let Some(base) = collapse {
        *e = (*base).clone();
    }
}

// ---------------------------------------------------------------------------
// Phase 2: type-reference rewrites
// ---------------------------------------------------------------------------

fn rewrite_type(ty: &mut Rc<Type>, elim: &HashSet<Rc<IdentT>>) {
    let t = Rc::make_mut(ty);
    match &mut t.val {
        TypeT::TypeRef(TypeRefKind::Union(n)) if elim.contains(&n.val) => {
            t.val = TypeT::TypeRef(TypeRefKind::Struct(n.clone()));
        }
        TypeT::Pointer(inner, _)
        | TypeT::FixedArray(inner, _)
        | TypeT::Nullable(inner)
        | TypeT::Plain(inner)
        | TypeT::Refine(inner, _)
        | TypeT::RefineAlways(inner, _)
        | TypeT::RefineUninit(inner, _) => rewrite_type(inner, elim),
        TypeT::RefineValue(inner, _, bty, _) => {
            rewrite_type(inner, elim);
            rewrite_type(bty, elim);
        }
        _ => {}
    }
}

fn rewrite_types_decl(decl: &mut DeclT, elim: &HashSet<Rc<IdentT>>) {
    match decl {
        DeclT::FnDefn(FnDefn { decl, body }) => {
            rewrite_types_fn_decl(decl, elim);
            rewrite_types_stmts(body, elim);
        }
        DeclT::FnDecl(fd) => rewrite_types_fn_decl(fd, elim),
        DeclT::Typedef(td) => rewrite_type(&mut td.body, elim),
        DeclT::StructDefn(StructDefn { fields, .. })
        | DeclT::UnionDefn(UnionDefn { fields, .. }) => {
            for f in fields.iter_mut() {
                rewrite_types_field(f, elim);
            }
        }
        DeclT::GlobalVar(GlobalVar { ty, init, .. }) => {
            rewrite_type(ty, elim);
            if let Some(e) = init {
                rewrite_types_expr(Rc::make_mut(e), elim);
            }
        }
        DeclT::LetDecl(ld) => {
            for p in ld.params.iter_mut() {
                rewrite_type(&mut p.ty, elim);
            }
            rewrite_type(&mut ld.ret_type, elim);
            for e in ld.requires.iter_mut().chain(ld.ensures.iter_mut()) {
                rewrite_types_expr(Rc::make_mut(e), elim);
            }
            rewrite_types_expr(Rc::make_mut(&mut ld.body), elim);
        }
        DeclT::StructDecl(_) | DeclT::IncludeDecl(_) | DeclT::OpaqueTypeDecl(_) => {}
    }
}

fn rewrite_types_field(f: &mut Field, elim: &HashSet<Rc<IdentT>>) {
    match &mut f.val {
        FieldT::Plain { ty, .. } | FieldT::BitField { ty, .. } => rewrite_type(ty, elim),
    }
}

fn rewrite_types_fn_decl(decl: &mut FnDecl, elim: &HashSet<Rc<IdentT>>) {
    for ga in decl.ghost_args.iter_mut() {
        rewrite_type(&mut ga.ty, elim);
    }
    for arg in decl.args.iter_mut() {
        rewrite_type(&mut arg.ty, elim);
    }
    rewrite_type(&mut decl.ret_type, elim);
    for e in decl.requires.iter_mut().chain(decl.ensures.iter_mut()) {
        rewrite_types_expr(Rc::make_mut(e), elim);
    }
}

fn rewrite_types_stmts(stmts: &mut Stmts, elim: &HashSet<Rc<IdentT>>) {
    for stmt in stmts.iter_mut() {
        rewrite_types_stmt(Rc::make_mut(stmt), elim);
    }
}

fn rewrite_types_stmt(stmt: &mut Stmt, elim: &HashSet<Rc<IdentT>>) {
    match &mut stmt.val {
        StmtT::Call(e) | StmtT::Assert(e) | StmtT::Return(Some(e)) => {
            rewrite_types_expr(Rc::make_mut(e), elim)
        }
        StmtT::Decl(_, ty) => rewrite_type(ty, elim),
        StmtT::DeclStackArray {
            elem_type, size, ..
        } => {
            rewrite_type(elem_type, elim);
            rewrite_types_expr(Rc::make_mut(size), elim);
        }
        StmtT::Assign(lhs, rhs) => {
            rewrite_types_expr(Rc::make_mut(lhs), elim);
            rewrite_types_expr(Rc::make_mut(rhs), elim);
        }
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ensures,
        } => {
            rewrite_types_expr(Rc::make_mut(cond), elim);
            rewrite_types_stmts(Rc::make_mut(then_branch), elim);
            rewrite_types_stmts(Rc::make_mut(else_branch), elim);
            for e in Rc::make_mut(ensures).iter_mut() {
                rewrite_types_expr(Rc::make_mut(e), elim);
            }
        }
        StmtT::While {
            cond,
            inv,
            requires,
            ensures,
            body,
        } => {
            rewrite_types_expr(Rc::make_mut(cond), elim);
            for e in Rc::make_mut(inv)
                .iter_mut()
                .chain(Rc::make_mut(requires).iter_mut())
                .chain(Rc::make_mut(ensures).iter_mut())
            {
                rewrite_types_expr(Rc::make_mut(e), elim);
            }
            rewrite_types_stmts(Rc::make_mut(body), elim);
        }
        StmtT::Label { ensures, .. } => {
            for e in Rc::make_mut(ensures).iter_mut() {
                rewrite_types_expr(Rc::make_mut(e), elim);
            }
        }
        StmtT::GotoBlock { body, ensures, .. } => {
            rewrite_types_stmts(Rc::make_mut(body), elim);
            for e in Rc::make_mut(ensures).iter_mut() {
                rewrite_types_expr(Rc::make_mut(e), elim);
            }
        }
        StmtT::Break
        | StmtT::Continue
        | StmtT::Return(None)
        | StmtT::GhostStmt(_)
        | StmtT::Goto(_)
        | StmtT::Error => {}
    }
}

fn rewrite_types_expr(e: &mut Expr, elim: &HashSet<Rc<IdentT>>) {
    match &mut e.val {
        ExprT::IntLit(_, ty)
        | ExprT::FloatLit(_, ty)
        | ExprT::InlinePulse(_, ty)
        | ExprT::Malloc(ty)
        | ExprT::Calloc(ty)
        | ExprT::SizeOf(ty)
        | ExprT::AlignOf(ty)
        | ExprT::Error(ty) => rewrite_type(ty, elim),
        ExprT::Cast(x, ty) | ExprT::MallocArray(ty, x) | ExprT::CallocArray(ty, x) => {
            rewrite_type(ty, elim);
            rewrite_types_expr(Rc::make_mut(x), elim);
        }
        ExprT::ContainerOf(x, ty, _) => {
            rewrite_type(ty, elim);
            rewrite_types_expr(Rc::make_mut(x), elim);
        }
        ExprT::Forall(_, ty, x) | ExprT::Exists(_, ty, x) => {
            rewrite_type(ty, elim);
            rewrite_types_expr(Rc::make_mut(x), elim);
        }
        ExprT::ArrayInit(ty, args) => {
            rewrite_type(ty, elim);
            for a in args.iter_mut() {
                rewrite_types_expr(Rc::make_mut(a), elim);
            }
        }
        ExprT::MemsetZero(ty, x) => {
            rewrite_type(ty, elim);
            rewrite_types_expr(Rc::make_mut(x), elim);
        }
        ExprT::Memset(ty, a, b, c) => {
            rewrite_type(ty, elim);
            rewrite_types_expr(Rc::make_mut(a), elim);
            rewrite_types_expr(Rc::make_mut(b), elim);
            rewrite_types_expr(Rc::make_mut(c), elim);
        }
        ExprT::Deref(x)
        | ExprT::Member(x, _)
        | ExprT::VAttr(_, x)
        | ExprT::Ref(x)
        | ExprT::UnOp(_, x)
        | ExprT::Live(x)
        | ExprT::Old(x)
        | ExprT::PreIncr(x)
        | ExprT::PostIncr(x)
        | ExprT::PreDecr(x)
        | ExprT::PostDecr(x)
        | ExprT::Free(x)
        | ExprT::UnionInit(_, _, x) => rewrite_types_expr(Rc::make_mut(x), elim),
        ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
            rewrite_types_expr(Rc::make_mut(a), elim);
            rewrite_types_expr(Rc::make_mut(b), elim);
        }
        ExprT::Cond(a, b, c) => {
            rewrite_types_expr(Rc::make_mut(a), elim);
            rewrite_types_expr(Rc::make_mut(b), elim);
            rewrite_types_expr(Rc::make_mut(c), elim);
        }
        ExprT::FnCall(_, args) => {
            for a in args.iter_mut() {
                rewrite_types_expr(Rc::make_mut(a), elim);
            }
        }
        ExprT::StructInit(_, kvs) => {
            for (_, v) in kvs.iter_mut() {
                rewrite_types_expr(Rc::make_mut(v), elim);
            }
        }
        ExprT::Var(_) | ExprT::BoolLit(_) => {}
    }
}
