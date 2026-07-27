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

fn param_renames(decl: &FnDecl, defn: &FnDecl) -> HashMap<Rc<str>, Rc<Ident>> {
    let mut renames = HashMap::new();
    for (decl_arg, defn_arg) in decl.args.iter().zip(defn.args.iter()) {
        let (Some(decl_name), Some(defn_name)) = (&decl_arg.name, &defn_arg.name) else {
            continue;
        };
        if decl_name.val != defn_name.val {
            renames.insert(decl_name.val.clone(), defn_name.clone());
        }
    }
    for (decl_arg, defn_arg) in decl.ghost_args.iter().zip(defn.ghost_args.iter()) {
        if decl_arg.name.val != defn_arg.name.val {
            renames.insert(decl_arg.name.val.clone(), defn_arg.name.clone());
        }
    }
    renames
}

fn rename_specs(exprs: &Exprs, renames: &HashMap<Rc<str>, Rc<Ident>>) -> Exprs {
    if renames.is_empty() {
        return exprs.clone();
    }
    exprs.iter().map(|e| rename_expr(e, renames)).collect()
}

fn rename_expr(expr: &Rc<Expr>, renames: &HashMap<Rc<str>, Rc<Ident>>) -> Rc<Expr> {
    let mut expr = expr.clone();
    rename_expr_in_place(Rc::make_mut(&mut expr), renames);
    expr
}

fn rename_shadowed_expr(
    binder: &Ident,
    body: &mut Rc<Expr>,
    renames: &HashMap<Rc<str>, Rc<Ident>>,
) {
    if renames.contains_key(&binder.val) {
        let mut shadowed = renames.clone();
        shadowed.remove(&binder.val);
        rename_expr_in_place(Rc::make_mut(body), &shadowed);
    } else {
        rename_expr_in_place(Rc::make_mut(body), renames);
    }
}

fn rename_expr_in_place(expr: &mut Expr, renames: &HashMap<Rc<str>, Rc<Ident>>) {
    match &mut expr.val {
        ExprT::Var(name) => {
            if let Some(new_name) = renames.get(&name.val) {
                *name = new_name.clone();
            }
        }
        ExprT::Deref(a)
        | ExprT::Ref(a)
        | ExprT::UnOp(_, a)
        | ExprT::Live(a)
        | ExprT::Old(a)
        | ExprT::PreIncr(a)
        | ExprT::PostIncr(a)
        | ExprT::PreDecr(a)
        | ExprT::PostDecr(a)
        | ExprT::Free(a)
        | ExprT::Member(a, _)
        | ExprT::VAttr(_, a) => rename_expr_in_place(Rc::make_mut(a), renames),
        ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
            rename_expr_in_place(Rc::make_mut(a), renames);
            rename_expr_in_place(Rc::make_mut(b), renames);
        }
        ExprT::ContainerOf(ptr, struct_ty, _) => {
            rename_expr_in_place(Rc::make_mut(ptr), renames);
            rename_type_in_place(Rc::make_mut(struct_ty), renames);
        }
        ExprT::Cond(a, b, c) => {
            rename_expr_in_place(Rc::make_mut(a), renames);
            rename_expr_in_place(Rc::make_mut(b), renames);
            rename_expr_in_place(Rc::make_mut(c), renames);
        }
        ExprT::FnCall(_, args) => {
            for arg in args {
                rename_expr_in_place(Rc::make_mut(arg), renames);
            }
        }
        ExprT::Cast(a, ty) => {
            rename_expr_in_place(Rc::make_mut(a), renames);
            rename_type_in_place(Rc::make_mut(ty), renames);
        }
        ExprT::InlinePulse(code, ty) => {
            rename_inline_pulse_in_place(Rc::make_mut(code), renames);
            rename_type_in_place(Rc::make_mut(ty), renames);
        }
        ExprT::Forall(binder, ty, body) | ExprT::Exists(binder, ty, body) => {
            rename_type_in_place(Rc::make_mut(ty), renames);
            rename_shadowed_expr(binder, body, renames);
        }
        ExprT::StructInit(_, fields) => {
            for (_, value) in fields {
                rename_expr_in_place(Rc::make_mut(value), renames);
            }
        }
        ExprT::UnionInit(_, _, value) => rename_expr_in_place(Rc::make_mut(value), renames),
        ExprT::ArrayInit {
            elem_ty: ty, elems, ..
        } => {
            rename_type_in_place(Rc::make_mut(ty), renames);
            for elem in elems {
                rename_expr_in_place(Rc::make_mut(elem), renames);
            }
        }
        ExprT::IntLit(_, ty)
        | ExprT::FloatLit(_, ty)
        | ExprT::Malloc(ty)
        | ExprT::Calloc(ty)
        | ExprT::SizeOf(ty)
        | ExprT::AlignOf(ty)
        | ExprT::Error(ty) => rename_type_in_place(Rc::make_mut(ty), renames),
        ExprT::MallocArray(ty, count) | ExprT::CallocArray(ty, count) => {
            rename_type_in_place(Rc::make_mut(ty), renames);
            rename_expr_in_place(Rc::make_mut(count), renames);
        }
        ExprT::MallocFlex(ty, count) | ExprT::CallocFlex(ty, count) => {
            rename_type_in_place(Rc::make_mut(ty), renames);
            rename_expr_in_place(Rc::make_mut(count), renames);
        }
        ExprT::Memset(ty, ptr, value, count) => {
            rename_type_in_place(Rc::make_mut(ty), renames);
            rename_expr_in_place(Rc::make_mut(ptr), renames);
            rename_expr_in_place(Rc::make_mut(value), renames);
            rename_expr_in_place(Rc::make_mut(count), renames);
        }
        ExprT::MemsetZero(ty, ptr) => {
            rename_type_in_place(Rc::make_mut(ty), renames);
            rename_expr_in_place(Rc::make_mut(ptr), renames);
        }
        ExprT::BoolLit(_) => {}
    }
}

fn rename_inline_pulse_in_place(code: &mut InlinePulseCode, renames: &HashMap<Rc<str>, Rc<Ident>>) {
    for token in &mut code.tokens {
        match token {
            InlinePulseToken::RValueAntiquot { expr, .. }
            | InlinePulseToken::LValueAntiquot { expr, .. } => {
                rename_expr_in_place(Rc::make_mut(expr), renames);
            }
            InlinePulseToken::TypeAntiquot { ty, .. }
            | InlinePulseToken::FieldAntiquot { ty, .. }
            | InlinePulseToken::AuxFnAntiquot { ty, .. }
            | InlinePulseToken::Declare { ty, .. } => {
                rename_type_in_place(Rc::make_mut(ty), renames);
            }
            InlinePulseToken::Verbatim(_) => {}
        }
    }
}

fn rename_type_in_place(ty: &mut Type, renames: &HashMap<Rc<str>, Rc<Ident>>) {
    match &mut ty.val {
        TypeT::Pointer(inner, _)
        | TypeT::FixedArray(inner, _)
        | TypeT::FlexArray(inner)
        | TypeT::Plain(inner)
        | TypeT::Nullable(inner) => rename_type_in_place(Rc::make_mut(inner), renames),
        TypeT::Refine(inner, pred)
        | TypeT::RefineAlways(inner, pred)
        | TypeT::RefineUninit(inner, pred) => {
            rename_type_in_place(Rc::make_mut(inner), renames);
            rename_expr_in_place(Rc::make_mut(pred), renames);
        }
        TypeT::RefineValue(inner, binder, binder_ty, pred) => {
            rename_type_in_place(Rc::make_mut(inner), renames);
            rename_type_in_place(Rc::make_mut(binder_ty), renames);
            rename_shadowed_expr(binder, pred, renames);
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
    // Track FnDecl specs to copy into their matching FnDefn before moves/removals.
    // The trailing Vec<GhostArg> holds the declaration's ghost arguments to
    // reintroduce into a definition that declared none (see below).
    let mut spec_copies: Vec<(usize, Exprs, Exprs, Vec<GhostArg>)> = Vec::new();

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

                    if decl_has_specs && !defn_has_specs {
                        let renames = param_renames(fn_decl, &defn.decl);
                        // The specs we copy below (and the definition's own body)
                        // reference the declaration's ghost-argument variables. If
                        // the definition declared no ghost args of its own, the
                        // emitted `fn` signature would omit those binders and F*
                        // would reject the module with "Identifier not found:
                        // var_<ghost>". Reintroduce the declaration's ghost args in
                        // that case. When the definition declares its own ghost args
                        // they are canonical (its body is written against them and
                        // `param_renames` maps the specs onto them), so keep them;
                        // a nonzero-but-different count is a genuine inconsistency.
                        let ghost_args_to_copy = if defn.decl.ghost_args.is_empty() {
                            fn_decl.ghost_args.clone()
                        } else {
                            if fn_decl.ghost_args.len() != defn.decl.ghost_args.len() {
                                report(
                                    diags,
                                    format!(
                                        "declaration of {} lists {} ghost argument(s) but its \
                                         definition lists {}; they must match (or the definition \
                                         may omit them entirely to inherit the declaration's)",
                                        fn_decl.name.val,
                                        fn_decl.ghost_args.len(),
                                        defn.decl.ghost_args.len()
                                    ),
                                    &fn_decl.name.loc,
                                );
                            }
                            Vec::new()
                        };
                        spec_copies.push((
                            defn_idx,
                            rename_specs(&fn_decl.requires, &renames),
                            rename_specs(&fn_decl.ensures, &renames),
                            ghost_args_to_copy,
                        ));
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

    // Copy specs from declarations into definitions before moving/removing them.
    for (defn_idx, requires, ensures, ghost_args) in spec_copies {
        if let DeclT::FnDefn(ref mut defn) = tu.decls[defn_idx].val {
            if defn.decl.requires.is_empty() && defn.decl.ensures.is_empty() {
                defn.decl.requires = requires;
                defn.decl.ensures = ensures;
            }
            if defn.decl.ghost_args.is_empty() && !ghost_args.is_empty() {
                defn.decl.ghost_args = ghost_args;
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

    // === Phase 3: Order type definitions before their dependents ===
    reorder_type_deps(tu);
}

/// A key uniquely identifying a type-defining declaration. The first component
/// disambiguates the namespace (typedef / struct / union) since a typedef and a
/// struct may share the same name (e.g. `typedef struct profile profile;`).
type TypeKey = (u8, Rc<str>);

const TYPEDEF_NS: u8 = 0;
const STRUCT_NS: u8 = 1;
const UNION_NS: u8 = 2;

/// Collect the type references that appear in a type expression, descending
/// through pointers, arrays and refinements (but not into the referenced type's
/// own definition). Emission of a struct/typedef predicate recurses through
/// these layers and references each referenced type's predicate (including
/// through pointers), so the referenced type's declaration must be emitted
/// first to register its spec parameters.
///
/// `core_ref` pointers are the exception: they erase their pointee type and
/// contribute no predicate/spec at emission, so they impose no ordering
/// constraint and are deliberately not descended into (doing so would create a
/// false dependency cycle for the recursive structs core_ref exists to break).
fn collect_type_refs(ty: &Type, out: &mut Vec<TypeKey>) {
    match &ty.val {
        // See the doc comment: `core_ref` imposes no emission-order dependency.
        TypeT::Pointer(_, PointerKind::Core) => {}
        TypeT::Pointer(inner, _) | TypeT::FixedArray(inner, _) | TypeT::Plain(inner) => {
            collect_type_refs(inner, out)
        }
        TypeT::Refine(inner, _)
        | TypeT::RefineAlways(inner, _)
        | TypeT::RefineUninit(inner, _)
        | TypeT::RefineValue(inner, _, _, _)
        | TypeT::Nullable(inner) => collect_type_refs(inner, out),
        TypeT::TypeRef(k) => {
            let key = match k {
                TypeRefKind::Typedef(n) => (TYPEDEF_NS, n.val.clone()),
                TypeRefKind::Struct(n) => (STRUCT_NS, n.val.clone()),
                TypeRefKind::Union(n) => (UNION_NS, n.val.clone()),
            };
            out.push(key);
        }
        _ => {}
    }
}

/// Collect type references appearing anywhere in an expression (in casts,
/// allocations, `sizeof`, quantifier binders, inline-Pulse antiquotations, etc.)
/// and recursively in its subexpressions.
fn collect_refs_expr(e: &Expr, out: &mut Vec<TypeKey>) {
    match &e.val {
        ExprT::Var(_) | ExprT::BoolLit(_) => {}
        ExprT::IntLit(_, ty) | ExprT::FloatLit(_, ty) | ExprT::Error(ty) => {
            collect_type_refs(ty, out)
        }
        ExprT::Deref(a)
        | ExprT::Ref(a)
        | ExprT::UnOp(_, a)
        | ExprT::Live(a)
        | ExprT::Old(a)
        | ExprT::PreIncr(a)
        | ExprT::PostIncr(a)
        | ExprT::PreDecr(a)
        | ExprT::PostDecr(a)
        | ExprT::Free(a)
        | ExprT::Member(a, _)
        | ExprT::VAttr(_, a) => collect_refs_expr(a, out),
        ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
            collect_refs_expr(a, out);
            collect_refs_expr(b, out);
        }
        ExprT::ContainerOf(ptr, struct_ty, _) => {
            collect_refs_expr(ptr, out);
            collect_type_refs(struct_ty, out);
        }
        ExprT::Cond(a, b, c) => {
            collect_refs_expr(a, out);
            collect_refs_expr(b, out);
            collect_refs_expr(c, out);
        }
        ExprT::FnCall(_, args) => {
            for a in args {
                collect_refs_expr(a, out);
            }
        }
        ExprT::Cast(a, ty) => {
            collect_refs_expr(a, out);
            collect_type_refs(ty, out);
        }
        ExprT::InlinePulse(code, ty) => {
            collect_refs_inline(code, out);
            collect_type_refs(ty, out);
        }
        ExprT::Forall(_, ty, body) | ExprT::Exists(_, ty, body) => {
            collect_type_refs(ty, out);
            collect_refs_expr(body, out);
        }
        ExprT::StructInit(_, fields) => {
            for (_, v) in fields {
                collect_refs_expr(v, out);
            }
        }
        ExprT::UnionInit(_, _, v) => collect_refs_expr(v, out),
        ExprT::ArrayInit {
            elem_ty: ty, elems, ..
        } => {
            collect_type_refs(ty, out);
            for el in elems {
                collect_refs_expr(el, out);
            }
        }
        ExprT::Malloc(ty) | ExprT::Calloc(ty) | ExprT::SizeOf(ty) | ExprT::AlignOf(ty) => {
            collect_type_refs(ty, out)
        }
        ExprT::MallocArray(ty, n) | ExprT::CallocArray(ty, n) => {
            collect_type_refs(ty, out);
            collect_refs_expr(n, out);
        }
        ExprT::MallocFlex(ty, n) | ExprT::CallocFlex(ty, n) => {
            collect_type_refs(ty, out);
            collect_refs_expr(n, out);
        }
        ExprT::Memset(ty, ptr, value, n) => {
            collect_type_refs(ty, out);
            collect_refs_expr(ptr, out);
            collect_refs_expr(value, out);
            collect_refs_expr(n, out);
        }
        ExprT::MemsetZero(ty, ptr) => {
            collect_type_refs(ty, out);
            collect_refs_expr(ptr, out);
        }
    }
}

/// Collect type references appearing in inline-Pulse code antiquotations.
fn collect_refs_inline(code: &InlinePulseCode, out: &mut Vec<TypeKey>) {
    for t in &code.tokens {
        match t {
            InlinePulseToken::RValueAntiquot { expr, .. }
            | InlinePulseToken::LValueAntiquot { expr, .. } => collect_refs_expr(expr, out),
            InlinePulseToken::TypeAntiquot { ty, .. }
            | InlinePulseToken::FieldAntiquot { ty, .. }
            | InlinePulseToken::AuxFnAntiquot { ty, .. }
            | InlinePulseToken::Declare { ty, .. } => collect_type_refs(ty, out),
            InlinePulseToken::Verbatim(_) => {}
        }
    }
}

/// Collect type references appearing in a statement and its substatements.
fn collect_refs_stmt(s: &Stmt, out: &mut Vec<TypeKey>) {
    let exprs = |es: &Exprs, out: &mut Vec<TypeKey>| {
        for e in es {
            collect_refs_expr(e, out);
        }
    };
    match &s.val {
        StmtT::Call(e) | StmtT::Assert(e) => collect_refs_expr(e, out),
        StmtT::Decl(_, ty) => collect_type_refs(ty, out),
        StmtT::Let(_, ty, value) => {
            collect_type_refs(ty, out);
            collect_refs_expr(value, out);
        }
        StmtT::DeclStackArray {
            elem_type, size, ..
        } => {
            collect_type_refs(elem_type, out);
            collect_refs_expr(size, out);
        }
        StmtT::Assign(a, b) => {
            collect_refs_expr(a, out);
            collect_refs_expr(b, out);
        }
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ensures,
        } => {
            collect_refs_expr(cond, out);
            for st in then_branch.iter() {
                collect_refs_stmt(st, out);
            }
            for st in else_branch.iter() {
                collect_refs_stmt(st, out);
            }
            exprs(ensures, out);
        }
        StmtT::Match {
            scrutinee,
            branches,
            default_branch,
            ensures,
        } => {
            collect_refs_expr(scrutinee, out);
            for branch in branches.iter() {
                exprs(&branch.patterns, out);
                for stmt in branch.body.iter() {
                    collect_refs_stmt(stmt, out);
                }
            }
            for stmt in default_branch.iter() {
                collect_refs_stmt(stmt, out);
            }
            exprs(ensures, out);
        }
        StmtT::While {
            cond,
            inv,
            requires,
            ensures,
            body,
        } => {
            collect_refs_expr(cond, out);
            exprs(inv, out);
            exprs(requires, out);
            exprs(ensures, out);
            for st in body.iter() {
                collect_refs_stmt(st, out);
            }
        }
        StmtT::Return(Some(e)) => collect_refs_expr(e, out),
        StmtT::GhostStmt(code) => collect_refs_inline(code, out),
        StmtT::Label { ensures, .. } => exprs(ensures, out),
        StmtT::GotoBlock { body, ensures, .. } => {
            for st in body.iter() {
                collect_refs_stmt(st, out);
            }
            exprs(ensures, out);
        }
        StmtT::Return(None) | StmtT::Break | StmtT::Continue | StmtT::Goto(_) | StmtT::Error => {}
    }
}
/// emitted after the type definitions it references by-value or by-pointer.
///
/// This is required because emission populates the spec-parameter tables for a
/// type when its predicate is emitted, and a dependent type's predicate reads
/// those tables. Earlier merge phases can hoist a struct definition to the
/// position of an earlier forward declaration (e.g. introduced by a forward
/// `typedef`), which would otherwise place a struct before an anonymous struct
/// lifted out of one of its fields.
fn reorder_type_deps(tu: &mut TranslationUnit) {
    let n = tu.decls.len();
    if n == 0 {
        return;
    }

    // Map each type-defining declaration to its key.
    let mut node_of_key: HashMap<TypeKey, usize> = HashMap::new();
    for (i, d) in tu.decls.iter().enumerate() {
        let key = match &d.val {
            DeclT::Typedef(t) => Some((TYPEDEF_NS, t.name.val.clone())),
            DeclT::StructDefn(s) => Some((STRUCT_NS, s.name.val.clone())),
            DeclT::UnionDefn(u) => Some((UNION_NS, u.name.val.clone())),
            _ => None,
        };
        if let Some(key) = key {
            node_of_key.insert(key, i);
        }
    }

    // Compute prerequisites: indices that must precede each declaration.
    let mut prereqs: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, d) in tu.decls.iter().enumerate() {
        let mut refs: Vec<TypeKey> = Vec::new();
        match &d.val {
            DeclT::Typedef(t) => collect_type_refs(&t.body, &mut refs),
            DeclT::StructDefn(s) => {
                for f in &s.fields {
                    collect_type_refs(&f.val.logical_type(&f.loc), &mut refs);
                }
            }
            DeclT::UnionDefn(u) => {
                for f in &u.fields {
                    collect_type_refs(&f.val.logical_type(&f.loc), &mut refs);
                }
            }
            // Functions, globals and let-definitions also reference type
            // predicates (via their signature types) when emitting specs, so
            // they must follow the type definitions they mention.
            DeclT::FnDecl(fd) => {
                collect_type_refs(&fd.ret_type, &mut refs);
                for a in &fd.args {
                    collect_type_refs(&a.ty, &mut refs);
                }
                for e in fd.requires.iter().chain(fd.ensures.iter()) {
                    collect_refs_expr(e, &mut refs);
                }
            }
            DeclT::FnDefn(fd) => {
                collect_type_refs(&fd.decl.ret_type, &mut refs);
                for a in &fd.decl.args {
                    collect_type_refs(&a.ty, &mut refs);
                }
                for e in fd.decl.requires.iter().chain(fd.decl.ensures.iter()) {
                    collect_refs_expr(e, &mut refs);
                }
                for st in fd.body.iter() {
                    collect_refs_stmt(st, &mut refs);
                }
            }
            DeclT::LetDecl(ld) => {
                collect_type_refs(&ld.ret_type, &mut refs);
                for a in &ld.params {
                    collect_type_refs(&a.ty, &mut refs);
                }
                for e in ld.requires.iter().chain(ld.ensures.iter()) {
                    collect_refs_expr(e, &mut refs);
                }
                collect_refs_expr(&ld.body, &mut refs);
            }
            DeclT::GlobalVar(gv) => collect_type_refs(&gv.ty, &mut refs),
            _ => {}
        }
        for r in refs {
            if let Some(&j) = node_of_key.get(&r) {
                if j != i {
                    prereqs[i].push(j);
                }
            }
        }
    }

    // Stable topological sort: repeatedly pick the lowest-indexed declaration
    // whose prerequisites are already placed. On a dependency cycle (e.g.
    // mutually pointer-referential structs), fall back to original order to
    // avoid looping.
    let mut done = vec![false; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    while order.len() < n {
        let picked = (0..n)
            .find(|&i| !done[i] && prereqs[i].iter().all(|&j| done[j]))
            .or_else(|| (0..n).find(|&i| !done[i]))
            .expect("at least one undone declaration");
        done[picked] = true;
        order.push(picked);
    }

    if order.iter().enumerate().any(|(pos, &i)| pos != i) {
        let mut old: Vec<Option<_>> = std::mem::take(&mut tu.decls)
            .into_iter()
            .map(Some)
            .collect();
        tu.decls = order.into_iter().map(|i| old[i].take().unwrap()).collect();
    }
}
