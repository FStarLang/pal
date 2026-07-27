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

use std::{collections::HashMap, rc::Rc};

use crate::{diag::Diagnostics, env::Env, ir::*, mayberc::MaybeRc};

/// Per-eliminated-union information.
struct ElimUnion {
    /// The two arm (field) names of the union.
    arm_names: Vec<Rc<IdentT>>,
    /// The shared CIS fields that become the fields of the replacement struct
    /// (used only when `named_struct` is `None`).
    cis_fields: Vec<Field>,
    /// If the named arm's type is a directly-named struct, its name. When set,
    /// the union collapses INTO that struct (reusing its nominal type) instead
    /// of synthesizing a fresh struct, so pointers to the named arm keep the
    /// arm's struct type (e.g. `&h->list : struct list*`).
    named_struct: Option<Rc<IdentT>>,
}

/// If `f`'s type resolves directly to a named struct, return that struct's name.
fn arm_struct_name(env: &Env, f: &Field) -> Option<Rc<IdentT>> {
    if f.val.bit_width().is_some() {
        return None;
    }
    let ty: MaybeRc<Type> = f.val.logical_type(&f.loc).into();
    let ty = env.vtype_whnf(ty);
    match &ty.val {
        TypeT::TypeRef(TypeRefKind::Struct(sname)) => Some(sname.val.clone()),
        _ => None,
    }
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
fn is_simple_cis(env: &Env, u: &UnionDefn) -> Option<(Vec<Field>, Option<Rc<IdentT>>)> {
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
    // If the named arm's type is a directly-named struct, reuse it as the
    // collapse target so pointers to the arm keep the arm's struct type.
    let named_arm = if is_anon(arm0) { arm1 } else { arm0 };
    let named_struct = arm_struct_name(env, named_arm);
    Some((s0, named_struct))
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
            if let Some((cis_fields, named_struct)) = is_simple_cis(&env, u) {
                let arm_names = u.fields.iter().map(|f| f.val.name().val.clone()).collect();
                elim.insert(
                    u.name.val.clone(),
                    ElimUnion {
                        arm_names,
                        cis_fields,
                        named_struct,
                    },
                );
            }
        }
    }
    if elim.is_empty() {
        return;
    }
    // Map each eliminated union to the struct it collapses into: the named
    // arm's struct when reusable, otherwise a fresh struct sharing the union's
    // own name.
    let elim_names: HashMap<Rc<IdentT>, Rc<IdentT>> = elim
        .iter()
        .map(|(uname, info)| {
            let target = info.named_struct.clone().unwrap_or_else(|| uname.clone());
            (uname.clone(), target)
        })
        .collect();

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

    // Phase 2: rewrite all `Union(u)` type references to the target struct
    // type, then for each eliminated `UnionDefn` either drop it (when it reuses
    // an existing named arm struct) or swap it for a fresh `StructDefn` holding
    // the shared CIS fields.
    for decl in tu.decls.iter_mut() {
        rewrite_types_decl(&mut decl.val, &elim_names);
    }
    for decl in tu.decls.iter_mut() {
        if let DeclT::UnionDefn(u) = &decl.val {
            if let Some(info) = elim.get(&u.name.val) {
                if info.named_struct.is_none() {
                    decl.val = DeclT::StructDefn(StructDefn {
                        name: u.name.clone(),
                        fields: info.cis_fields.clone(),
                        eager_unfold_pred: false,
                    });
                }
            }
        }
    }
    // Drop the union defns that collapsed into an existing named arm struct;
    // their type references have already been redirected to that struct.
    tu.decls.retain(|decl| {
        if let DeclT::UnionDefn(u) = &decl.val {
            if let Some(info) = elim.get(&u.name.val) {
                return info.named_struct.is_none();
            }
        }
        true
    });
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
        StmtT::Let(_, _, value) => rewrite_expr(env, Rc::make_mut(value), elim),
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
        StmtT::Match {
            scrutinee,
            branches,
            default_branch,
            ensures,
        } => {
            rewrite_expr(env, Rc::make_mut(scrutinee), elim);
            for branch in Rc::make_mut(branches) {
                let branch = Rc::make_mut(branch);
                for pattern in Rc::make_mut(&mut branch.patterns) {
                    rewrite_expr(env, Rc::make_mut(pattern), elim);
                }
                rewrite_stmts(env, Rc::make_mut(&mut branch.body), elim);
            }
            rewrite_stmts(env, Rc::make_mut(default_branch), elim);
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
        | ExprT::MallocFlex(_, x)
        | ExprT::CallocFlex(_, x)
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
        ExprT::FnCall(_, args) | ExprT::ArrayInit { elems: args, .. } => {
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

    // Rewrite a cast `(struct F*)e` where `e : struct S*` and `S`'s first field
    // is an eliminated simple-CIS union whose named arm is `struct F`. Per C, a
    // pointer to a struct also points to its first member, so the cast is the
    // well-defined `&e->firstfield`. The frontend leaves this as a `Cast`
    // because at parse time the first field is still a union (not `struct F`);
    // after this pass collapses the union the first field *is* `struct F`, so
    // the coercion becomes valid and downstream `emit` handles the produced
    // `&e->_unnamed0` member/ref node directly (a raw struct*->struct* `Cast`
    // has no `emit` lowering).
    let cast_rw = if let ExprT::Cast(inner, target_ty) = &e.val {
        cast_to_first_member(env, inner, target_ty, &e.loc, elim)
    } else {
        None
    };
    if let Some(newval) = cast_rw {
        e.val = newval;
        return;
    }

    // Rewrite `UnionInit(u, arm, StructInit(_, kvs))` -> `StructInit(S, kvs)`,
    // where `S` is the struct the union collapses into (the reused named arm
    // struct, or the union's own name for the synthesize-fresh case).
    let uinit = if let ExprT::UnionInit(uname, _arm, val) = &e.val {
        if let Some(info) = elim.get(&uname.val) {
            if let ExprT::StructInit(_sname, kvs) = &val.val {
                let target = info
                    .named_struct
                    .clone()
                    .unwrap_or_else(|| uname.val.clone());
                let sname = Rc::new(Ast {
                    val: target,
                    loc: uname.loc.clone(),
                });
                Some((sname, kvs.clone()))
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };
    if let Some((sname, kvs)) = uinit {
        e.val = ExprT::StructInit(sname, kvs);
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

/// For a cast `(struct F*)inner`, if `inner : struct S*` and `S`'s first field
/// is an eliminated simple-CIS union whose named arm is `struct F`, build the
/// equivalent `&(*inner).firstfield` node (the collapse turns that first field
/// into `struct F`, so the member access has the cast's target type). Returns
/// the replacement `ExprT`, or `None` when the shape does not match.
fn cast_to_first_member(
    env: &Env,
    inner: &Rc<Expr>,
    target_ty: &Rc<Type>,
    loc: &Rc<SourceInfo>,
    elim: &HashMap<Rc<IdentT>, ElimUnion>,
) -> Option<ExprT> {
    // Target must be a pointer to a named struct `F`.
    let target = env.vtype_whnf(target_ty.clone().into());
    let TypeT::Pointer(f_pointee, _) = &target.val else {
        return None;
    };
    let f_pointee = env.vtype_whnf(f_pointee.clone().into());
    let TypeT::TypeRef(TypeRefKind::Struct(fname)) = &f_pointee.val else {
        return None;
    };

    // `inner` must be a pointer to a named struct `S`.
    let src = env.vtype_whnf(env.infer_expr(inner).ok()?);
    let TypeT::Pointer(s_pointee, _) = &src.val else {
        return None;
    };
    let s_pointee = env.vtype_whnf(s_pointee.clone().into());
    let TypeT::TypeRef(TypeRefKind::Struct(sname)) = &s_pointee.val else {
        return None;
    };

    // `S`'s first field must be an eliminated simple-CIS union whose named arm
    // is `struct F`.
    let s = env.lookup_struct(sname)?;
    let first = s.fields.first()?;
    let first_ty = env.vtype_whnf(first.val.logical_type(&first.loc).into());
    let TypeT::TypeRef(TypeRefKind::Union(uname)) = &first_ty.val else {
        return None;
    };
    let info = elim.get(&uname.val)?;
    match &info.named_struct {
        Some(n) if **n == *fname.val => {}
        _ => return None,
    }

    // Build `&(*inner).firstfield`.
    let field_name: Rc<Ident> = Rc::new(first.val.name().clone());
    let deref = ExprT::Deref(inner.clone()).with_loc(loc.clone());
    let member = ExprT::Member(deref, field_name).with_loc(loc.clone());
    Some(ExprT::Ref(member))
}

// ---------------------------------------------------------------------------
// Phase 2: type-reference rewrites
// ---------------------------------------------------------------------------

fn rewrite_type(ty: &mut Rc<Type>, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
    let t = Rc::make_mut(ty);
    match &mut t.val {
        TypeT::TypeRef(TypeRefKind::Union(n)) if elim.contains_key(&n.val) => {
            let target = elim.get(&n.val).unwrap().clone();
            let name = Rc::new(Ast {
                val: target,
                loc: n.loc.clone(),
            });
            t.val = TypeT::TypeRef(TypeRefKind::Struct(name));
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

fn rewrite_types_decl(decl: &mut DeclT, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
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

fn rewrite_types_field(f: &mut Field, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
    match &mut f.val {
        FieldT::Plain { ty, .. } | FieldT::BitField { ty, .. } => rewrite_type(ty, elim),
    }
}

fn rewrite_types_fn_decl(decl: &mut FnDecl, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
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

fn rewrite_types_stmts(stmts: &mut Stmts, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
    for stmt in stmts.iter_mut() {
        rewrite_types_stmt(Rc::make_mut(stmt), elim);
    }
}

fn rewrite_types_stmt(stmt: &mut Stmt, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
    match &mut stmt.val {
        StmtT::Call(e) | StmtT::Assert(e) | StmtT::Return(Some(e)) => {
            rewrite_types_expr(Rc::make_mut(e), elim)
        }
        StmtT::Decl(_, ty) => rewrite_type(ty, elim),
        StmtT::Let(_, ty, value) => {
            rewrite_type(ty, elim);
            rewrite_types_expr(Rc::make_mut(value), elim);
        }
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
        StmtT::Match {
            scrutinee,
            branches,
            default_branch,
            ensures,
        } => {
            rewrite_types_expr(Rc::make_mut(scrutinee), elim);
            for branch in Rc::make_mut(branches) {
                let branch = Rc::make_mut(branch);
                for pattern in Rc::make_mut(&mut branch.patterns) {
                    rewrite_types_expr(Rc::make_mut(pattern), elim);
                }
                rewrite_types_stmts(Rc::make_mut(&mut branch.body), elim);
            }
            rewrite_types_stmts(Rc::make_mut(default_branch), elim);
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

fn rewrite_types_expr(e: &mut Expr, elim: &HashMap<Rc<IdentT>, Rc<IdentT>>) {
    match &mut e.val {
        ExprT::IntLit(_, ty)
        | ExprT::FloatLit(_, ty)
        | ExprT::InlinePulse(_, ty)
        | ExprT::Malloc(ty)
        | ExprT::Calloc(ty)
        | ExprT::SizeOf(ty)
        | ExprT::AlignOf(ty)
        | ExprT::Error(ty) => rewrite_type(ty, elim),
        ExprT::Cast(x, ty)
        | ExprT::MallocArray(ty, x)
        | ExprT::CallocArray(ty, x)
        | ExprT::MallocFlex(ty, x)
        | ExprT::CallocFlex(ty, x) => {
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
        ExprT::ArrayInit {
            elem_ty: ty,
            elems: args,
            ..
        } => {
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
