use num_bigint::BigInt;

use crate::diag::{Diagnostic, DiagnosticLevel, Diagnostics};
use crate::env::{Env, LocalDeclKind};
use crate::ir::*;
use crate::mayberc::MaybeRc;
use std::collections::HashMap;
use std::rc::Rc;

/// Position-independent key identifying the pointee of a pointer type, used to
/// look up a registered default pointer-view (`_pointer_view`).
#[derive(PartialEq, Eq, Hash, Clone)]
enum PointeeKey {
    Typedef(Rc<IdentT>),
    Struct(Rc<IdentT>),
    Union(Rc<IdentT>),
}

impl PointeeKey {
    fn from_kind(k: &TypeRefKind) -> Self {
        match k {
            TypeRefKind::Typedef(t) => PointeeKey::Typedef(t.val.clone()),
            TypeRefKind::Struct(s) => PointeeKey::Struct(s.val.clone()),
            TypeRefKind::Union(u) => PointeeKey::Union(u.val.clone()),
        }
    }

    /// Canonicalize a pointee type reference by resolving typedef aliases down
    /// to their underlying struct/union tag, so that `node *` and
    /// `struct node *` (where `node` is `typedef struct node {…} node;`) map to
    /// the same key.
    fn canon(env: &Env, k: &TypeRefKind) -> Self {
        let mut cur = k.clone();
        while let TypeRefKind::Typedef(n) = &cur {
            match env.lookup_type(n).map(|d| d.body.val.clone()) {
                Some(TypeT::TypeRef(inner)) => cur = inner,
                _ => break,
            }
        }
        PointeeKey::from_kind(&cur)
    }
}

struct Elaborator<'a> {
    diags: &'a mut Diagnostics,
    /// Map from a pointee type to the typedef registered (via `_pointer_view`)
    /// as the default view for pointers to that type.
    pointer_views: HashMap<PointeeKey, Rc<Ident>>,
    /// When true, default pointer-view substitution is suppressed (inside
    /// inline-Pulse code).
    in_inline_pulse: bool,
    /// When true, we are elaborating the body of a `_pointer_view` typedef, so
    /// substitution is suppressed to avoid self-recursive predicates.
    in_view_body: bool,
    /// When true, the next type visited is exempt from pointer-view substitution
    /// (set by `_plain` to keep the directly-wrapped pointer bare).
    suppress_next_view: bool,
}

fn cast_to(rval: &mut Rc<Expr>, ty: Rc<Type>) {
    *rval = ExprT::Cast(rval.clone(), ty).with_loc(rval.loc.clone())
}

/// Resolve a member access through anonymous (`_unnamed*`) struct/union members.
///
/// When a direct field lookup for `target` fails on the struct/union named by
/// `container`, C's anonymous-member transparency allows the field to live in a
/// nested anonymous member. This searches only anonymous members and returns the
/// chain of intermediate anonymous member names leading to a container that
/// directly holds `target` (`Some(vec![])` would mean `target` is direct — never
/// returned here since callers only invoke it after a failed direct lookup), or
/// `None` if `target` is unreachable this way.
///
/// This is needed for member accesses written in spec position (`_requires` /
/// `_ensures` / `assert`), where PAL's own parser produces a flat member chain
/// rather than the clang-resolved nested chain seen in function bodies.
fn indirect_field_path(
    env: &Env,
    container: &TypeRefKind,
    target: &Rc<Ident>,
) -> Option<Vec<Rc<Ident>>> {
    let fields: &[Field] = match container {
        TypeRefKind::Struct(n) => &env.lookup_struct(n)?.fields,
        TypeRefKind::Union(n) => &env.lookup_union(n)?.fields,
        TypeRefKind::Typedef(_) => return None,
    };
    if fields.iter().any(|f| f.val.name().val == target.val) {
        return Some(vec![]);
    }
    for f in fields {
        let fname = f.val.name();
        if !fname.val.starts_with("_unnamed") {
            continue;
        }
        let fty = env.vtype_whnf(f.val.logical_type(&f.loc).into());
        if let TypeT::TypeRef(inner) = &fty.val {
            if let Some(mut sub) = indirect_field_path(env, inner, target) {
                let mut path = vec![Rc::new(fname.clone())];
                path.append(&mut sub);
                return Some(path);
            }
        }
    }
    None
}

impl<'a> Elaborator<'a> {
    fn report(&mut self, msg: String, loc: &SourceInfo) {
        self.diags.report(Diagnostic {
            loc: loc.location().clone(),
            level: DiagnosticLevel::Error,
            msg: msg,
        });
    }

    fn infer_expr(&mut self, env: &Env, rval: &Expr) -> Option<MaybeRc<Type>> {
        match env.infer_expr(rval) {
            Ok(ty) => Some(ty),
            Err(error) => {
                self.report(
                    format!("cannot infer type of {}: {}\n{}", rval, error, env),
                    &rval.loc,
                );
                None
            }
        }
    }

    /// Reject a whole-object assignment whose target is a struct containing a
    /// flexible array member. In C such an assignment copies only the fixed
    /// part of the struct, not the flexible array contents (whether any of the
    /// array is copied at all depends on padding/alignment), so PAL cannot
    /// model it soundly. This covers both a copy from another object
    /// (`*a = *b`) and a compound-literal initializer (`*v = (struct vec){…}`):
    /// a struct with a flexible array member may not appear as the target of a
    /// whole-object assignment. Construct such a struct by zero-initializing it
    /// (e.g. `calloc`) and writing its fixed fields individually instead.
    fn check_flex_array_assign(&mut self, env: &Env, lhs: &Expr, _rhs: &Expr) {
        if let Ok(lhs_ty) = env.infer_expr(lhs)
            && env.type_has_flex_array_member(lhs_ty)
        {
            self.report(
                "assignment of a struct with a flexible array member is not supported: \
                 the flexible array contents are not copied by assignment in C; \
                 zero-initialize the struct (e.g. via calloc) and set its fixed fields \
                 individually instead"
                    .to_string(),
                &lhs.loc,
            );
        }
    }

    fn elab_field(&mut self, env: &Env, field: &mut Field, siblings: &[Field]) {
        match &mut field.val {
            FieldT::Plain { name, ty } => {
                // A flexible-array-member `_refines(...)` length refinement may
                // reference sibling fields (e.g. `len`) by name, so bring the
                // other fields into scope before elaborating the refinement.
                if matches!(&ty.val, TypeT::RefineAlways(inner, _) if matches!(peel_type(inner).val, TypeT::FlexArray(_)))
                {
                    let env = &mut env.clone();
                    for s in siblings {
                        let sname = s.val.name();
                        if sname.val != name.val {
                            env.push_var_decl(
                                sname,
                                s.val.logical_type(&s.loc),
                                LocalDeclKind::RValue,
                            );
                        }
                    }
                    self.elab_type(env, Rc::make_mut(ty));
                } else {
                    self.elab_type(env, Rc::make_mut(ty));
                }
            }
            FieldT::BitField { name: _, ty, .. } => self.elab_type(env, Rc::make_mut(ty)),
        }
    }

    /// Apply the default pointer-view substitution if `ty` is a bare pointer
    /// (`Ref`/`Unknown`) to a pointee with a registered `_pointer_view` typedef.
    /// Replaces `ty` in place with a reference to that typedef. Suppressed inside
    /// inline-Pulse code, inside a view typedef's own body, and for the single
    /// type directly following `_plain`.
    fn maybe_apply_view(&mut self, env: &Env, ty: &mut Type) {
        let suppressed = self.suppress_next_view;
        self.suppress_next_view = false;
        if suppressed || self.in_inline_pulse || self.in_view_body {
            return;
        }
        let TypeT::Pointer(to, kind) = &ty.val else {
            return;
        };
        if !matches!(kind, PointerKind::Ref | PointerKind::Unknown) {
            return;
        }
        let TypeT::TypeRef(k) = &to.val else {
            return;
        };
        if let Some(view_name) = self.pointer_views.get(&PointeeKey::canon(env, k)) {
            ty.val = TypeT::TypeRef(TypeRefKind::Typedef(view_name.clone()));
        }
    }

    fn elab_type(&mut self, env: &Env, ty: &mut Type) {
        self.maybe_apply_view(env, ty);
        match &mut ty.val {
            TypeT::Int {
                signed: _,
                width: _,
            } => {}
            TypeT::Float { width: _ } => {}
            TypeT::SizeT => {}
            TypeT::PtrdiffT => {}
            TypeT::Pointer(to, kind) => {
                self.elab_type(env, Rc::make_mut(to));
                match kind {
                    PointerKind::Unknown => *kind = PointerKind::Ref,
                    PointerKind::Ref => {}
                    PointerKind::Array => {}
                    PointerKind::ArrayPtr => {}
                    PointerKind::Core => {}
                }
            }
            TypeT::FixedArray(elem_ty, _) => {
                self.elab_type(env, Rc::make_mut(elem_ty));
            }
            TypeT::FlexArray(elem_ty) => {
                self.elab_type(env, Rc::make_mut(elem_ty));
            }
            TypeT::FnPtr { args, ret } => {
                for a in args.iter_mut() {
                    self.elab_type(env, Rc::make_mut(a));
                }
                self.elab_type(env, Rc::make_mut(ret));
            }
            TypeT::Unknown => {}
            TypeT::Error => {}
            TypeT::Void => {}
            TypeT::SLProp => {}
            TypeT::SpecInt | TypeT::SpecNat => {}
            TypeT::Bool => {}

            TypeT::TypeRef(_) => {}

            TypeT::Refine(ty, p) | TypeT::RefineAlways(ty, p) | TypeT::RefineUninit(ty, p) => {
                self.elab_type(env, Rc::make_mut(ty));

                let env = &mut env.clone();
                env.push_this(ty.clone());
                let slprop_ty = TypeT::SLProp.with_loc(p.loc.clone());
                self.elab_rvalue(env, Rc::make_mut(p), Some(&slprop_ty));
                self.cast_to_slprop(env, p);
            }
            TypeT::RefineValue(ty, binding_name, binding_ty, p) => {
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_type(env, Rc::make_mut(binding_ty));

                let env = &mut env.clone();
                env.push_this(ty.clone());
                env.push_var_decl(binding_name, binding_ty.clone(), LocalDeclKind::RValue);
                let slprop_ty = TypeT::SLProp.with_loc(p.loc.clone());
                self.elab_rvalue(env, Rc::make_mut(p), Some(&slprop_ty));
                self.cast_to_slprop(env, p);
            }
            TypeT::Plain(ty) => {
                self.suppress_next_view = true;
                self.elab_type(env, Rc::make_mut(ty));
            }
            TypeT::Nullable(ty) => self.elab_type(env, Rc::make_mut(ty)),
        }
    }

    fn elab_lvalue(&mut self, env: &Env, lval: &mut Expr) {
        self.elab_rvalue(env, lval, None);
        if !env.is_lvalue(lval) {
            self.report(format!("expected lvalue, got {}", lval), &lval.loc);
        }
    }

    fn cast_to_slprop(&mut self, env: &Env, rval: &mut Rc<Expr>) {
        if env
            .infer_expr(rval)
            .ok()
            .filter(|p| env.is_slprop(p.clone()))
            .is_none()
        {
            *rval = ExprT::Cast(rval.clone(), TypeT::SLProp.with_loc(rval.loc.clone()))
                .with_loc(rval.loc.clone())
        }
    }

    fn cast_to_bool(&mut self, env: &Env, rval: &mut Rc<Expr>) {
        if env
            .infer_expr(rval)
            .ok()
            .filter(|p| env.is_bool(p.clone()))
            .is_none()
        {
            *rval = ExprT::Cast(rval.clone(), TypeT::Bool.with_loc(rval.loc.clone()))
                .with_loc(rval.loc.clone())
        }
    }

    fn elab_inline_pulse_code(&mut self, env: &Env, code: &mut InlinePulseCode) {
        let env = &mut env.clone();
        let prev_in_inline_pulse = self.in_inline_pulse;
        self.in_inline_pulse = true;
        for tok in &mut code.tokens {
            match tok {
                InlinePulseToken::RValueAntiquot { expr, .. }
                | InlinePulseToken::LValueAntiquot { expr, .. } => {
                    self.elab_rvalue(env, Rc::make_mut(expr), None)
                }
                InlinePulseToken::TypeAntiquot { ty, .. } => self.elab_type(env, Rc::make_mut(ty)),
                InlinePulseToken::Declare { ident, ty, .. } => {
                    self.elab_type(env, Rc::make_mut(ty));
                    env.push_var_decl(ident, ty.clone(), LocalDeclKind::RValue);
                }
                InlinePulseToken::Verbatim(_) | InlinePulseToken::FieldAntiquot { .. } => {}
                InlinePulseToken::AuxFnAntiquot { ty, .. } => self.elab_type(env, Rc::make_mut(ty)),
            }
        }
        self.in_inline_pulse = prev_in_inline_pulse;
    }

    fn elab_rvalue(&mut self, env: &Env, rval: &mut Expr, expected: Option<&Type>) {
        match &mut rval.val {
            ExprT::Var(_) => {}
            ExprT::Deref(v) => self.elab_rvalue(env, Rc::make_mut(v), None),
            ExprT::Member(x, a) => {
                self.elab_rvalue(env, Rc::make_mut(x), None);
                // Convert _active on union member → VAttr::Active
                if &*a.val == "_active" {
                    if let ExprT::Member(base, fld) = &x.val {
                        if let Ok(t) = env.infer_expr(base) {
                            let t = env.vtype_whnf(t);
                            if let TypeT::TypeRef(TypeRefKind::Union(n)) = &t.val {
                                let Some(u) = env.lookup_union(n) else {
                                    return self.report(format!("unknown union {}", n), &rval.loc);
                                };
                                if u.get_field(fld).is_none() {
                                    return self.report(
                                        format!("no field {} in union {}", fld, n),
                                        &rval.loc,
                                    );
                                }
                                rval.val = ExprT::VAttr(VAttr::Active(fld.clone()), base.clone());
                                return;
                            }
                        }
                    }
                }
                if let Ok(t) = env.infer_expr(x) {
                    // Own `x`/`a` so the branches below may reassign `rval.val`.
                    let x = x.clone();
                    let a = a.clone();
                    let t = env.vtype_whnf(t);
                    let mut indirect: Option<Vec<Rc<Ident>>> = None;
                    match &t.val {
                        // Convert _length on array → VAttr::Length
                        TypeT::Pointer(_, PointerKind::Array) if &*a.val == "_length" => {
                            rval.val = ExprT::VAttr(VAttr::Length, x.clone());
                        }
                        TypeT::FixedArray(_, _) if &*a.val == "_length" => {
                            rval.val = ExprT::VAttr(VAttr::Length, x.clone());
                        }
                        TypeT::FlexArray(_) if &*a.val == "_length" => {
                            rval.val = ExprT::VAttr(VAttr::Length, x.clone());
                        }
                        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
                            let Some(s) = env.lookup_struct(n) else {
                                return self.report(format!("unknown structure {}", n), &rval.loc);
                            };
                            if s.get_field(&a).is_none() {
                                match indirect_field_path(env, &TypeRefKind::Struct(n.clone()), &a)
                                {
                                    Some(path) => indirect = Some(path),
                                    None => {
                                        return self.report(
                                            format!("no field {} in structure {}", a, n),
                                            &rval.loc,
                                        );
                                    }
                                }
                            }
                        }
                        TypeT::TypeRef(TypeRefKind::Union(n)) => {
                            let Some(u) = env.lookup_union(n) else {
                                return self.report(format!("unknown union {}", n), &rval.loc);
                            };
                            if u.get_field(&a).is_none() {
                                match indirect_field_path(env, &TypeRefKind::Union(n.clone()), &a) {
                                    Some(path) => indirect = Some(path),
                                    None => {
                                        return self.report(
                                            format!("no field {} in union {}", a, n),
                                            &rval.loc,
                                        );
                                    }
                                }
                            }
                        }
                        _ => {
                            return self.report(format!("not a structure type: {}", t), &rval.loc);
                        }
                    }
                    // A member reachable only through anonymous members (e.g. a
                    // spec-position access parsed into a flat chain): rewrite it
                    // into the nested chain and re-elaborate.
                    if let Some(path) = indirect {
                        let mut base = x.clone();
                        for g in &path {
                            base = ExprT::Member(base, g.clone()).with_loc(rval.loc.clone());
                        }
                        rval.val = ExprT::Member(base, a.clone());
                        self.elab_rvalue(env, rval, expected);
                    }
                }
            }
            ExprT::VAttr(_, x) => {
                self.elab_rvalue(env, Rc::make_mut(x), None);
            }
            ExprT::Index(arr, idx) => {
                self.elab_rvalue(env, Rc::make_mut(arr), None);
                self.elab_rvalue(env, Rc::make_mut(idx), None);
                // Cast index to SizeT for Pulse array operations
                if let Ok(idx_ty) = env.infer_expr(idx) {
                    let idx_ty_whnf = env.vtype_whnf(idx_ty);
                    if !matches!(idx_ty_whnf.val, TypeT::SizeT) {
                        cast_to(idx, TypeT::SizeT.with_loc(idx.loc.clone()));
                    }
                }
            }
            ExprT::IntLit(_, ty) | ExprT::FloatLit(_, ty) => self.elab_type(env, Rc::make_mut(ty)),
            ExprT::Ref(v) => {
                self.elab_rvalue(env, Rc::make_mut(v), None);
                // C defines `&E1[E2]` as `(E1) + (E2)`. When E1 is one of
                // PAL's array-shaped pointers (which aren't true memory
                // arrays at the Pulse level), rewrite to a BinOp::Add so
                // that emission goes through the pointer-arithmetic path
                // instead of trying to manufacture an lvalue for the
                // element. The index would otherwise be lost in the
                // implicit Array→ArrayPtr coercion at the call site.
                if let ExprT::Index(arr, idx) = &v.val {
                    let arr_kind = env
                        .infer_expr(arr)
                        .ok()
                        .map(|t| env.vtype_whnf(t))
                        .and_then(|t| match &t.val {
                            TypeT::Pointer(_, k @ (PointerKind::Array | PointerKind::ArrayPtr)) => {
                                Some(k.clone())
                            }
                            _ => None,
                        });
                    // When `&a[i]` is expected to produce a plain `int *`
                    // (PointerKind::Ref) and `a` is a real `_array`, keep the
                    // node as `Ref(Index)`. Emission borrows a Pulse `ref` from
                    // the array cell at that index. The default rewrite to
                    // `a + i` (an arrayptr) only applies otherwise.
                    let expected_is_ref = expected
                        .map(|t| env.vtype_whnf(t.clone().into()))
                        .is_some_and(|t| matches!(&t.val, TypeT::Pointer(_, PointerKind::Ref)));
                    let borrow_to_ref = expected_is_ref && arr_kind == Some(PointerKind::Array);
                    let arr_is_array_ptr = arr_kind.is_some() && !borrow_to_ref;
                    if arr_is_array_ptr {
                        let arr = arr.clone();
                        let idx = idx.clone();
                        rval.val = ExprT::BinOp(BinOp::Add, arr, idx);
                        // Re-elaborate as a BinOp::Add. The new node isn't
                        // a Ref, so this rewrite arm can't re-fire and the
                        // recursion terminates.
                        self.elab_rvalue(env, rval, expected);
                        return;
                    }
                }
                if !env.is_lvalue(v) {
                    self.report(format!("expected lvalue for &, got {}", v), &rval.loc);
                }
            }
            ExprT::FnCall(f, args) => {
                // Collect param types before elaborating args (to pass expected types)
                let param_types: Option<Vec<_>> = env
                    .lookup_fn(f)
                    .map(|fn_decl| fn_decl.args.iter().map(|arg| arg.ty.clone()).collect());
                for (i, arg) in args.iter_mut().enumerate() {
                    let expected_param = param_types
                        .as_ref()
                        .and_then(|pts| pts.get(i))
                        .map(|t| t.as_ref());
                    self.elab_rvalue(env, Rc::make_mut(arg), expected_param);
                }
                if let Some(param_types) = param_types {
                    for (arg, param_ty) in args.iter_mut().zip(param_types.iter()) {
                        let expected_ty = env.vtype_whnf(param_ty.clone().into());
                        if let Ok(actual_ty) = env.infer_expr(arg) {
                            if !env.vtype_eq(actual_ty, expected_ty.clone()) {
                                cast_to(arg, (*expected_ty).clone().into());
                            }
                        }
                    }
                }
            }
            ExprT::FnRef(_) => {}
            ExprT::FnPtrCall(f, args) => {
                self.elab_rvalue(env, Rc::make_mut(f), None);
                // Collect the callee's parameter types (tupled arg types of the
                // FnPtr) to pass expected types into the arguments.
                let param_types: Option<Vec<Rc<Type>>> = env
                    .infer_expr(f)
                    .ok()
                    .map(|t| env.vtype_whnf(t))
                    .and_then(|t| match &t.val {
                        TypeT::FnPtr { args, .. } => Some(args.clone()),
                        _ => None,
                    });
                for (i, arg) in args.iter_mut().enumerate() {
                    let expected_param = param_types
                        .as_ref()
                        .and_then(|pts| pts.get(i))
                        .map(|t| t.as_ref());
                    self.elab_rvalue(env, Rc::make_mut(arg), expected_param);
                }
                if let Some(param_types) = param_types {
                    for (arg, param_ty) in args.iter_mut().zip(param_types.iter()) {
                        let expected_ty = env.vtype_whnf(param_ty.clone().into());
                        if let Ok(actual_ty) = env.infer_expr(arg) {
                            if !env.vtype_eq(actual_ty, expected_ty.clone()) {
                                cast_to(arg, (*expected_ty).clone().into());
                            }
                        }
                    }
                }
            }
            ExprT::Cast(val, ty) => {
                let val = Rc::make_mut(val);
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_rvalue(env, val, Some(ty));
                let _actual_ty = env.infer_expr(val);
                // TODO: check that actual_ty can be casted to ty
            }
            ExprT::Error(ty) => self.elab_type(env, Rc::make_mut(ty)),
            ExprT::SizeOf(ty) | ExprT::AlignOf(ty) => self.elab_type(env, Rc::make_mut(ty)),
            ExprT::Malloc(ty) | ExprT::Calloc(ty) => self.elab_type(env, Rc::make_mut(ty)),
            ExprT::MallocArray(ty, count) | ExprT::CallocArray(ty, count) => {
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_rvalue(env, Rc::make_mut(count), None);
                if let Ok(count_ty) = env.infer_expr(count) {
                    if !matches!(&env.vtype_whnf(count_ty).val, TypeT::SizeT) {
                        cast_to(count, TypeT::SizeT.with_loc(count.loc.clone()));
                    }
                }
            }
            ExprT::MallocFlex(ty, count) | ExprT::CallocFlex(ty, count) => {
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_rvalue(env, Rc::make_mut(count), None);
                if let Ok(count_ty) = env.infer_expr(count) {
                    if !matches!(&env.vtype_whnf(count_ty).val, TypeT::SizeT) {
                        cast_to(count, TypeT::SizeT.with_loc(count.loc.clone()));
                    }
                }
            }
            ExprT::Memset(ty, ptr, value, count) => {
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_rvalue(env, Rc::make_mut(ptr), None);
                self.elab_rvalue(env, Rc::make_mut(value), Some(ty));
                if let Ok(value_ty) = env.infer_expr(value) {
                    if !env.vtype_eq(value_ty, ty.clone().into()) {
                        cast_to(value, ty.clone());
                    }
                }
                self.elab_rvalue(env, Rc::make_mut(count), None);
                if let Ok(count_ty) = env.infer_expr(count) {
                    if !matches!(&env.vtype_whnf(count_ty).val, TypeT::SizeT) {
                        cast_to(count, TypeT::SizeT.with_loc(count.loc.clone()));
                    }
                }
            }
            ExprT::MemsetZero(ty, ptr) => {
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_rvalue(env, Rc::make_mut(ptr), None);
            }
            ExprT::Free(val) => self.elab_rvalue(env, Rc::make_mut(val), None),
            ExprT::ContainerOf(ptr, struct_ty, _) => {
                self.elab_rvalue(env, Rc::make_mut(ptr), None);
                self.elab_type(env, Rc::make_mut(struct_ty));
            }
            ExprT::PreIncr(val)
            | ExprT::PostIncr(val)
            | ExprT::PreDecr(val)
            | ExprT::PostDecr(val) => self.elab_lvalue(env, Rc::make_mut(val)),
            ExprT::InlinePulse(code, ty) => {
                if matches!(ty.val, TypeT::Unknown) {
                    if let Some(exp) = expected {
                        *Rc::make_mut(ty) = exp.clone();
                    } else {
                        self.report(
                            "cannot infer type of _inline_pulse; add an explicit type cast"
                                .to_string(),
                            &rval.loc,
                        );
                    }
                }
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_inline_pulse_code(env, Rc::make_mut(code));
            }
            ExprT::UnOp(un_op, arg) => {
                self.elab_rvalue(env, Rc::make_mut(arg), None);
                match un_op {
                    UnOp::Not => self.cast_to_bool(env, arg),
                    UnOp::Neg | UnOp::BitNot => {}
                }
            }
            ExprT::BinOp(bin_op, lhs, rhs) => {
                self.elab_rvalue(env, Rc::make_mut(lhs), None);
                self.elab_rvalue(env, Rc::make_mut(rhs), None);
                let Some(lhs_ty) = self.infer_expr(env, lhs) else {
                    return;
                };
                let Some(rhs_ty) = self.infer_expr(env, rhs) else {
                    return;
                };
                if *bin_op == BinOp::Eq {
                    let lhs_ty = env.vtype_whnf(lhs_ty.clone());
                    if let TypeT::Pointer(_, _) = &lhs_ty.val {
                        if let ExprT::IntLit(n, rhs_ty) = &mut Rc::make_mut(rhs).val {
                            if **n == BigInt::ZERO {
                                *rhs_ty = lhs_ty.to_rc();
                                return;
                            }
                        }
                        if let ExprT::Cast(inner, rhs_ty) = &mut Rc::make_mut(rhs).val
                            && matches!(&inner.val, ExprT::IntLit(n, _) if **n == BigInt::ZERO)
                            && matches!(
                                &env.vtype_whnf(rhs_ty.clone().into()).val,
                                TypeT::Pointer(_, _)
                            )
                        {
                            *rhs_ty = lhs_ty.to_rc();
                            return;
                        }
                    }
                    // Mixed pointer-kind equality (e.g. arrayptr == ref): the two
                    // abstract pointer types are not directly comparable, so
                    // erase both operands to raw `core_ref` addresses and compare
                    // there (emit lowers `(Eq, Core)` to `core_ref_eq`). Only
                    // fires when the pointees agree so we never bridge unrelated
                    // pointers.
                    let lhs_w = env.vtype_whnf(lhs_ty.clone());
                    let rhs_w = env.vtype_whnf(rhs_ty.clone());
                    if let (
                        TypeT::Pointer(lhs_pointee, lhs_kind),
                        TypeT::Pointer(rhs_pointee, rhs_kind),
                    ) = (&lhs_w.val, &rhs_w.val)
                        && lhs_kind != rhs_kind
                        && *lhs_kind != PointerKind::Core
                        && *rhs_kind != PointerKind::Core
                        && env.vtype_eq(lhs_pointee.clone().into(), rhs_pointee.clone().into())
                    {
                        cast_to(
                            lhs,
                            TypeT::Pointer(lhs_pointee.clone(), PointerKind::Core)
                                .with_loc(lhs.loc.clone()),
                        );
                        cast_to(
                            rhs,
                            TypeT::Pointer(rhs_pointee.clone(), PointerKind::Core)
                                .with_loc(rhs.loc.clone()),
                        );
                        return;
                    }
                }
                match bin_op {
                    BinOp::LogAnd | BinOp::LogOr | BinOp::Implies => {
                        // For SLProp operands, use meet_type casts (&&→**, etc.)
                        // For non-SLProp operands, cast to Bool (handles int→bool)
                        let meet = env.meet_type(lhs_ty.clone(), rhs_ty.clone());
                        let is_slprop = meet
                            .as_ref()
                            .map(|t| matches!(env.vtype_whnf(t.clone()).val, TypeT::SLProp))
                            .unwrap_or(false);
                        if is_slprop {
                            if let Some(meet_type) = meet {
                                if !env.vtype_eq(lhs_ty, meet_type.clone()) {
                                    cast_to(lhs, meet_type.clone().to_rc())
                                }
                                if !env.vtype_eq(rhs_ty, meet_type.clone()) {
                                    cast_to(rhs, meet_type.to_rc())
                                }
                            }
                        } else {
                            self.cast_to_bool(env, lhs);
                            self.cast_to_bool(env, rhs);
                        }
                    }
                    BinOp::Eq
                    | BinOp::LEq
                    | BinOp::Lt
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::Add
                    | BinOp::Sub
                    | BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::BitXor => {
                        // Pointer arithmetic: array/arrayptr ± integer → cast integer to SizeT
                        let lhs_w = env.vtype_whnf(lhs_ty.clone());
                        let rhs_w = env.vtype_whnf(rhs_ty.clone());
                        let lhs_is_ptr = matches!(
                            &lhs_w.val,
                            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                        );
                        let rhs_is_ptr = matches!(
                            &rhs_w.val,
                            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                        );
                        if lhs_is_ptr && !rhs_is_ptr && matches!(bin_op, BinOp::Add | BinOp::Sub) {
                            let rhs_w = env.vtype_whnf(rhs_ty.clone());
                            if !matches!(rhs_w.val, TypeT::SizeT) {
                                cast_to(rhs, TypeT::SizeT.with_loc(rhs.loc.clone()));
                            }
                            return;
                        }
                        if rhs_is_ptr && !lhs_is_ptr && matches!(bin_op, BinOp::Add) {
                            let lhs_w = env.vtype_whnf(lhs_ty.clone());
                            if !matches!(lhs_w.val, TypeT::SizeT) {
                                cast_to(lhs, TypeT::SizeT.with_loc(lhs.loc.clone()));
                            }
                            return;
                        }
                        if let Some(mut meet_type) = env.meet_type(lhs_ty.clone(), rhs_ty.clone()) {
                            // C integer promotion: Bool → int for arithmetic/bitwise ops
                            if env.is_bool(meet_type.clone())
                                && matches!(
                                    bin_op,
                                    BinOp::Add
                                        | BinOp::Sub
                                        | BinOp::Mul
                                        | BinOp::Div
                                        | BinOp::Mod
                                        | BinOp::BitAnd
                                        | BinOp::BitOr
                                        | BinOp::BitXor
                                )
                            {
                                meet_type = TypeT::Int {
                                    signed: true,
                                    width: 32,
                                }
                                .with_loc(lhs.loc.clone())
                                .into();
                            }
                            if !env.vtype_eq(lhs_ty, meet_type.clone()) {
                                cast_to(lhs, meet_type.clone().to_rc())
                            }
                            if !env.vtype_eq(rhs_ty, meet_type.clone()) {
                                cast_to(rhs, meet_type.to_rc())
                            }
                        } else {
                            self.report(
                                format!(
                                    "cannot apply {} to arguments of type {} and {}",
                                    bin_op, lhs_ty, rhs_ty
                                ),
                                &rval.loc,
                            );
                        }
                    }
                    BinOp::Shl | BinOp::Shr => {
                        let u32_ty: MaybeRc<Type> = TypeT::Int {
                            signed: false,
                            width: 32,
                        }
                        .with_loc(rhs.loc.clone())
                        .into();
                        if !env.vtype_eq(rhs_ty, u32_ty.clone()) {
                            cast_to(rhs, u32_ty.to_rc())
                        }
                    }
                }
            }
            ExprT::BoolLit(_) => {}
            ExprT::Live(val) => self.elab_rvalue(env, Rc::make_mut(val), None),
            ExprT::Old(val) => self.elab_rvalue(env, Rc::make_mut(val), None),
            ExprT::Forall(var, ty, body) | ExprT::Exists(var, ty, body) => {
                let mut env = env.clone();
                env.push_var_decl(var, ty.clone(), LocalDeclKind::RValue);
                self.elab_rvalue(&env, Rc::make_mut(body), None);
            }
            ExprT::StructInit(name, fields) => {
                if env.lookup_type(name).is_some() {
                    let ty = TypeT::TypeRef(TypeRefKind::Typedef(name.clone()))
                        .with_loc(name.loc.clone());
                    if let TypeT::TypeRef(TypeRefKind::Struct(struct_name)) =
                        &env.vtype_whnf(ty.into()).val
                    {
                        *name = struct_name.clone();
                    }
                }
                let field_types: Vec<Option<Rc<Type>>> = fields
                    .iter()
                    .map(|(fld_name, _)| {
                        env.lookup_struct(name).and_then(|s| s.get_field(fld_name))
                    })
                    .collect();
                for ((_fld_name, fld_val), expected_ty) in fields.iter_mut().zip(field_types) {
                    self.elab_rvalue(env, Rc::make_mut(fld_val), expected_ty.as_deref());
                    if let Some(exp) = expected_ty {
                        if let Ok(v_ty) = env.infer_expr(fld_val) {
                            if !env.vtype_eq(v_ty, exp.clone().into()) {
                                cast_to(fld_val, exp);
                            }
                        }
                    }
                }
            }
            ExprT::UnionInit(_, _, fld_val) => {
                self.elab_rvalue(env, Rc::make_mut(fld_val), None);
            }
            ExprT::ArrayInit { elems, .. } => {
                for elem in elems {
                    self.elab_rvalue(env, Rc::make_mut(elem), None);
                }
            }
            ExprT::Cond(cond, then_expr, else_expr) => {
                self.elab_rvalue(env, Rc::make_mut(cond), None);
                self.cast_to_bool(env, cond);
                self.elab_rvalue(env, Rc::make_mut(then_expr), expected);
                self.elab_rvalue(env, Rc::make_mut(else_expr), expected);
                // Unify branch types
                let then_ty = env.infer_expr(then_expr).ok();
                let else_ty = env.infer_expr(else_expr).ok();
                if let (Some(t_ty), Some(e_ty)) = (then_ty, else_ty) {
                    if let Some(meet) = env.meet_type(t_ty.clone(), e_ty.clone()) {
                        if !env.vtype_eq(t_ty, meet.clone()) {
                            cast_to(then_expr, meet.clone().to_rc());
                        }
                        if !env.vtype_eq(e_ty, meet.clone()) {
                            cast_to(else_expr, meet.to_rc());
                        }
                    }
                }
            }
            ExprT::AssignExpr(lhs, rhs) => {
                self.elab_lvalue(env, Rc::make_mut(lhs));
                let lhs_ty = env.infer_expr(lhs).ok();
                let expected_rhs = lhs_ty.as_deref();
                self.elab_rvalue(env, Rc::make_mut(rhs), expected_rhs);
                self.check_flex_array_assign(env, lhs, rhs);
                // Cast RHS to LHS type if needed
                if let (Ok(x_ty), Ok(v_ty)) = (env.infer_expr(lhs), env.infer_expr(rhs)) {
                    if !env.vtype_eq(x_ty.clone(), v_ty) {
                        cast_to(rhs, x_ty.to_rc());
                    }
                }
            }
        }
    }

    fn elab_stmt(&mut self, env: &Env, stmt: &mut Stmt) {
        match &mut stmt.val {
            StmtT::Call(rval) => self.elab_rvalue(env, Rc::make_mut(rval), None),
            StmtT::Decl(_, ty) => self.elab_type(env, Rc::make_mut(ty)),
            StmtT::Let(_, ty, value) => {
                self.elab_type(env, Rc::make_mut(ty));
                self.elab_rvalue(env, Rc::make_mut(value), Some(ty));
                if let Ok(value_ty) = env.infer_expr(value)
                    && !env.vtype_eq(value_ty, ty.clone().into())
                {
                    cast_to(value, ty.clone());
                }
            }
            StmtT::DeclStackArray {
                elem_type, size, ..
            } => {
                self.elab_type(env, Rc::make_mut(elem_type));
                self.elab_rvalue(env, Rc::make_mut(size), None);
                // Cast size to SizeT if needed
                if let Ok(size_ty) = env.infer_expr(size) {
                    let size_ty = env.vtype_whnf(size_ty);
                    if !matches!(&size_ty.val, TypeT::SizeT) {
                        let target_ty = TypeT::SizeT.with_loc(size.loc.clone());
                        cast_to(size, target_ty);
                    }
                }
            }
            StmtT::Assign(x, v) => {
                self.elab_lvalue(env, Rc::make_mut(x));
                let x_ty = env.infer_expr(x).ok();
                let expected_v = x_ty.as_deref();
                self.elab_rvalue(env, Rc::make_mut(v), expected_v);
                self.check_flex_array_assign(env, x, v);
                let Ok(x_ty) = env.infer_expr(x) else {
                    return;
                };
                let Ok(v_ty) = env.infer_expr(v) else {
                    return;
                };
                if !env.vtype_eq(x_ty.clone(), v_ty.clone()) {
                    // Don't cast if the only difference is pointer kind refinement
                    let x_whnf = env.vtype_whnf(x_ty.clone());
                    let v_whnf = env.vtype_whnf(v_ty.clone());
                    let is_kind_refinement = matches!(
                        (&x_whnf.val, &v_whnf.val),
                        (
                            TypeT::Pointer(_, PointerKind::Unknown | PointerKind::Ref),
                            TypeT::Pointer(_, PointerKind::Array)
                        )
                    );
                    if !is_kind_refinement {
                        cast_to(v, x_ty.to_rc());
                    }
                }
            }
            StmtT::If {
                cond,
                then_branch,
                else_branch,
                ensures,
            } => {
                let bool_ty = TypeT::Bool.with_loc(cond.loc.clone());
                self.elab_rvalue(env, Rc::make_mut(cond), Some(&bool_ty));
                self.cast_to_bool(env, cond);
                self.elab_slprops(env, Rc::make_mut(ensures));
                self.elab_stmts(env, Rc::make_mut(then_branch));
                self.elab_stmts(env, Rc::make_mut(else_branch));
            }
            StmtT::Match {
                scrutinee,
                branches,
                default_branch,
                ensures,
            } => {
                self.elab_rvalue(env, Rc::make_mut(scrutinee), None);
                let scrutinee_ty = env.infer_expr(scrutinee).ok();
                for branch in Rc::make_mut(branches) {
                    let branch = Rc::make_mut(branch);
                    for pattern in Rc::make_mut(&mut branch.patterns) {
                        self.elab_rvalue(env, Rc::make_mut(pattern), scrutinee_ty.as_deref());
                    }
                    self.elab_stmts(env, Rc::make_mut(&mut branch.body));
                }
                self.elab_stmts(env, Rc::make_mut(default_branch));
                self.elab_slprops(env, Rc::make_mut(ensures));
            }
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => {
                let bool_ty = TypeT::Bool.with_loc(cond.loc.clone());
                self.elab_rvalue(env, Rc::make_mut(cond), Some(&bool_ty));
                self.cast_to_bool(env, cond);
                self.elab_slprops(env, Rc::make_mut(inv));
                for r in Rc::make_mut(requires) {
                    let bool_ty = TypeT::Bool.with_loc(r.loc.clone());
                    self.elab_rvalue(env, Rc::make_mut(r), Some(&bool_ty));
                    self.cast_to_bool(env, r);
                }
                for e in Rc::make_mut(ensures) {
                    let bool_ty = TypeT::Bool.with_loc(e.loc.clone());
                    self.elab_rvalue(env, Rc::make_mut(e), Some(&bool_ty));
                    self.cast_to_bool(env, e);
                }
                self.elab_stmts(env, Rc::make_mut(body));
            }
            StmtT::Break | StmtT::Continue => {}
            StmtT::Return(x) => {
                if let Some(x) = x {
                    let expected_ret = env.return_type.as_ref().map(|t| t.as_ref());
                    self.elab_rvalue(env, Rc::make_mut(x), expected_ret);
                    if let Some(ret_ty) = &env.return_type {
                        if let Ok(v_ty) = env.infer_expr(x) {
                            if !env.vtype_eq(v_ty, ret_ty.clone().into()) {
                                cast_to(x, ret_ty.clone());
                            }
                        }
                    }
                }
            }
            StmtT::Assert(v) => {
                let slprop_ty = TypeT::SLProp.with_loc(v.loc.clone());
                self.elab_rvalue(env, Rc::make_mut(v), Some(&slprop_ty));
                self.cast_to_slprop(env, v);
            }
            StmtT::GhostStmt(code) => self.elab_inline_pulse_code(env, Rc::make_mut(code)),
            StmtT::Goto(_) => {}
            StmtT::Label { ensures, .. } => {
                self.elab_slprops(env, Rc::make_mut(ensures));
            }
            StmtT::GotoBlock {
                body,
                label: _,
                ensures,
            } => {
                self.elab_stmts(env, Rc::make_mut(body));
                self.elab_slprops(env, Rc::make_mut(ensures));
            }
            StmtT::Error => {}
        }
    }

    /// Look ahead from a Decl to find a following assignment that refines the
    /// pointer kind (e.g. `int *a = malloc(sizeof(int) * 10)` → Array), and
    /// update the Decl's type before it is pushed to the environment.
    fn refine_decl_pointer_kind(env: &Env, stmts: &mut Vec<Rc<Stmt>>, decl_idx: usize) {
        let StmtT::Decl(decl_name, _) = &stmts[decl_idx].val else {
            return;
        };
        let var_name = &decl_name.val;
        for j in (decl_idx + 1)..stmts.len() {
            let StmtT::Assign(x, v) = &stmts[j].val else {
                continue;
            };
            let ExprT::Var(assign_name) = &x.val else {
                continue;
            };
            if assign_name.val != *var_name {
                continue;
            }
            let Ok(v_ty) = env.infer_expr(v) else {
                break;
            };
            let TypeT::Pointer(_, rhs_kind) = &env.vtype_whnf(v_ty).val else {
                break;
            };
            // A Core (`_core_ref`) initializer must not retype the local: the
            // local keeps its declared `ref T` kind, and the Core→Ref mismatch
            // is reconciled by an explicit `core_to_ref` coercion inserted at
            // the assignment (see elab_stmt/Assign + emit's Cast lowering).
            // Without this, the local would silently become an untyped
            // `core_ref` and lose its pointee type.
            //
            // An ArrayPtr initializer likewise must not retype a plain-pointer
            // (`ref T`) local to an arrayptr: a plain-pointer declaration is
            // taken to mean "borrow the pointed-at cell into a `ref`" (the
            // ArrayPtr→Ref mismatch is reconciled by a cast at the assignment,
            // which emit lowers to `arrayptr_borrow_cell`). Locals that should
            // stay arrayptrs -- e.g. ones built by pointer arithmetic -- must be
            // declared `_arrayptr` explicitly.
            if matches!(
                rhs_kind,
                PointerKind::Unknown | PointerKind::Core | PointerKind::ArrayPtr
            ) {
                break;
            }
            if let StmtT::Decl(_, decl_ty) = &mut Rc::make_mut(&mut stmts[decl_idx]).val {
                if let TypeT::Pointer(_, kind) = &mut Rc::make_mut(decl_ty).val {
                    if *kind == PointerKind::Unknown || *kind == PointerKind::Ref {
                        *kind = rhs_kind.clone();
                    }
                }
            }
            break;
        }
    }

    /// Lower complex expressions at the top of statements.
    /// - `Cond` in Assign/Return/Call → If statement
    fn lower_expr(stmt: &mut Rc<Stmt>) -> bool {
        let s = Rc::make_mut(stmt);
        let loc = s.loc.clone();
        match &s.val {
            StmtT::Assign(lhs, rhs) => {
                if let ExprT::Cond(c, a, b) = &rhs.val {
                    let (c, a, b, lhs) = (c.clone(), a.clone(), b.clone(), lhs.clone());
                    s.val = StmtT::If {
                        cond: c,
                        then_branch: Rc::new(vec![
                            StmtT::Assign(lhs.clone(), a).with_loc(loc.clone()),
                        ]),
                        else_branch: Rc::new(vec![StmtT::Assign(lhs, b).with_loc(loc)]),
                        ensures: Rc::new(vec![]),
                    };
                    return true;
                }
            }
            StmtT::Return(Some(rhs)) => {
                if let ExprT::Cond(c, a, b) = &rhs.val {
                    let (c, a, b) = (c.clone(), a.clone(), b.clone());
                    s.val = StmtT::If {
                        cond: c,
                        then_branch: Rc::new(vec![StmtT::Return(Some(a)).with_loc(loc.clone())]),
                        else_branch: Rc::new(vec![StmtT::Return(Some(b)).with_loc(loc)]),
                        ensures: Rc::new(vec![]),
                    };
                    return true;
                }
            }
            StmtT::Call(rhs) => {
                if let ExprT::Cond(c, a, b) = &rhs.val {
                    let (c, a, b) = (c.clone(), a.clone(), b.clone());
                    s.val = StmtT::If {
                        cond: c,
                        then_branch: Rc::new(vec![StmtT::Call(a).with_loc(loc.clone())]),
                        else_branch: Rc::new(vec![StmtT::Call(b).with_loc(loc)]),
                        ensures: Rc::new(vec![]),
                    };
                    return true;
                }
            }
            _ => {}
        }
        false
    }

    fn elab_stmts(&mut self, env: &Env, stmts: &mut Vec<Rc<Stmt>>) {
        let mut env = env.clone();
        let mut i = 0;
        while i < stmts.len() {
            Self::refine_decl_pointer_kind(&env, stmts, i);

            self.elab_stmt(&env, Rc::make_mut(&mut stmts[i]));
            Self::lower_expr(&mut stmts[i]);
            env.push_stmt(&stmts[i]);
            i += 1;
        }
    }

    fn elab_slprops(&mut self, env: &Env, slprops: &mut Vec<Rc<Expr>>) {
        for p in slprops {
            let slprop_ty = TypeT::SLProp.with_loc(p.loc.clone());
            self.elab_rvalue(env, Rc::make_mut(p), Some(&slprop_ty));
            self.cast_to_slprop(env, p);
        }
    }

    fn elab_fn_decl(
        &mut self,
        env: &Env,
        FnDecl {
            name: _,
            ret_type,
            args,
            ghost_args,
            requires,
            ensures,
            is_pure: _,
            is_rec: _,
            is_total: _,
            decreases,
        }: &mut FnDecl,
    ) {
        let env = &mut env.clone();
        for ga in ghost_args {
            self.elab_type(env, Rc::make_mut(&mut ga.ty));
            env.push_var_decl(&ga.name, ga.ty.clone(), LocalDeclKind::RValue);
        }
        for arg in args {
            self.elab_type(env, Rc::make_mut(&mut arg.ty));
            env.push_arg(arg, LocalDeclKind::RValue);
        }
        self.elab_slprops(env, requires);
        self.elab_type(env, Rc::make_mut(ret_type));
        env.push_return(ret_type.clone());
        self.elab_slprops(env, ensures);
        if let Some(dec) = decreases {
            self.elab_rvalue(env, Rc::make_mut(dec), None);
            // Machine-integer decreases measures (e.g. `hi - lo` of type
            // size_t) are not well-founded under F*'s `<<` relation, so
            // termination checking fails. Coerce them to mathematical
            // integers (`SpecInt`), which emits e.g. `SizeT.v (...)`.
            if let Ok(dec_ty) = env.infer_expr(dec) {
                if matches!(
                    &env.vtype_whnf(dec_ty).val,
                    TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT
                ) {
                    cast_to(dec, TypeT::SpecInt.with_loc(dec.loc.clone()));
                }
            }
        }
    }

    fn elab_decl(&mut self, env: &Env, decl: &mut Decl) {
        // TODO: check double definition
        match &mut decl.val {
            DeclT::FnDefn(FnDefn { decl, body }) => {
                self.elab_fn_decl(env, decl);
                let env = &mut env.clone();
                env.push_fn_decl_args_for_body(decl);
                self.elab_stmts(env, body);
            }
            DeclT::FnDecl(fn_decl) => self.elab_fn_decl(env, fn_decl),
            DeclT::Typedef(typedef) => {
                self.in_view_body = typedef.is_pointer_view;
                self.elab_type(env, Rc::make_mut(&mut typedef.body));
                self.in_view_body = false;
            }
            DeclT::StructDefn(StructDefn {
                name: _, fields, ..
            }) => {
                let siblings = fields.clone();
                for f in fields {
                    self.elab_field(env, f, &siblings);
                }
            }
            DeclT::StructDecl(_) => {}
            DeclT::UnionDefn(UnionDefn { name: _, fields }) => {
                let siblings = fields.clone();
                for f in fields {
                    self.elab_field(env, f, &siblings);
                }
            }
            DeclT::IncludeDecl(include_decl) => {
                self.elab_inline_pulse_code(env, &mut include_decl.code)
            }
            DeclT::OpaqueTypeDecl(decl) => self.elab_inline_pulse_code(env, &mut decl.code),
            DeclT::LetDecl(let_decl) => {
                self.elab_type(env, Rc::make_mut(&mut let_decl.ret_type));
                for arg in &mut let_decl.params {
                    self.elab_type(env, Rc::make_mut(&mut arg.ty));
                }
                let env = &mut env.clone();
                for arg in &let_decl.params {
                    env.push_arg(arg, LocalDeclKind::LValue);
                }
                for r in &mut let_decl.requires {
                    self.elab_rvalue(env, Rc::make_mut(r), None);
                }
                for e in &mut let_decl.ensures {
                    self.elab_rvalue(env, Rc::make_mut(e), None);
                }
                let ret_type = let_decl.ret_type.clone();
                self.elab_rvalue(env, Rc::make_mut(&mut let_decl.body), Some(&ret_type));
                if matches!(ret_type.val, TypeT::SLProp) {
                    self.cast_to_slprop(env, &mut let_decl.body);
                } else if let Ok(v_ty) = env.infer_expr(&let_decl.body) {
                    if !env.vtype_eq(v_ty, ret_type.clone().into()) {
                        cast_to(&mut let_decl.body, ret_type);
                    }
                }
            }
            DeclT::GlobalVar(GlobalVar {
                name: _,
                ty,
                init,
                is_pure: _,
                opaque_to_smt: _,
            }) => {
                self.elab_type(env, Rc::make_mut(ty));
                if let Some(init) = init {
                    self.elab_rvalue(env, Rc::make_mut(init), Some(ty));
                }
            }
        }
    }
}

/// Find the named pointee `TypeRefKind` of a `_pointer_view` typedef body by
/// stripping refinement/`Plain`/`Nullable` wrappers down to the inner pointer.
/// Returns `None` if the body is not (a wrapped) pointer to a named type.
fn view_pointee(body: &Type) -> Option<&TypeRefKind> {
    match &body.val {
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, _, _, _)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => view_pointee(t),
        TypeT::Pointer(to, _) => match &to.val {
            TypeT::TypeRef(k) => Some(k),
            _ => None,
        },
        _ => None,
    }
}

/// Scan the translation unit for `_pointer_view` typedefs and build a map from
/// pointee type to the registering typedef. Reports a diagnostic for views whose
/// body is not a pointer to a named type, and for duplicate views of the same
/// pointee.
fn build_pointer_views(
    diags: &mut Diagnostics,
    env: &Env,
    tu: &TranslationUnit,
) -> HashMap<PointeeKey, Rc<Ident>> {
    let mut views: HashMap<PointeeKey, Rc<Ident>> = HashMap::new();
    for decl in &tu.decls {
        let DeclT::Typedef(td) = &decl.val else {
            continue;
        };
        if !td.is_pointer_view {
            continue;
        }
        let Some(k) = view_pointee(&td.body) else {
            diags.report(Diagnostic {
                loc: td.name.loc.location().clone(),
                level: DiagnosticLevel::Error,
                msg: format!(
                    "_pointer_view typedef `{}` must be a pointer to a named type",
                    td.name
                ),
            });
            continue;
        };
        let key = PointeeKey::canon(env, k);
        if let Some(existing) = views.get(&key) {
            diags.report(Diagnostic {
                loc: td.name.loc.location().clone(),
                level: DiagnosticLevel::Error,
                msg: format!(
                    "duplicate _pointer_view for the same pointee: `{}` conflicts with `{}`",
                    td.name, existing
                ),
            });
            continue;
        }
        views.insert(key, td.name.clone());
    }
    views
}

pub fn elab(diags: &mut Diagnostics, tu: &mut TranslationUnit) {
    let mut env = Env::new();
    // Pre-register every declaration so that elaboration is order-independent
    // (e.g. an `_include_pulse` block in one file can refer to a typedef
    // declared in another file, and a function body can call another function
    // defined later in the translation unit). Elaboration of each decl below
    // pushes the elaborated version into the environment, overwriting this
    // initial entry.
    for decl in tu.decls.iter() {
        env.push_decl(decl);
    }
    // Build the default pointer-view map now that every typedef is registered,
    // so pointee keys can be canonicalized through typedef aliases.
    let pointer_views = build_pointer_views(diags, &env, tu);
    let mut elab = Elaborator {
        diags,
        pointer_views,
        in_inline_pulse: false,
        in_view_body: false,
        suppress_next_view: false,
    };
    // Pre-pass: elaborate the type-level parts of each declaration (function
    // signatures, typedef bodies, struct/union fields, etc.) and re-register
    // the elaborated version. This ensures that when we later elaborate a
    // function body or `_include_pulse` block, every cross-reference resolves
    // to a properly elaborated type (e.g. pointer kinds promoted from Unknown
    // to Ref) regardless of declaration order.
    for decl in &mut tu.decls {
        match &mut decl.val {
            DeclT::FnDefn(FnDefn { decl: fn_decl, .. }) | DeclT::FnDecl(fn_decl) => {
                let env = &mut env.clone();
                for ga in &mut fn_decl.ghost_args {
                    elab.elab_type(env, Rc::make_mut(&mut ga.ty));
                }
                for arg in &mut fn_decl.args {
                    elab.elab_type(env, Rc::make_mut(&mut arg.ty));
                }
                elab.elab_type(env, Rc::make_mut(&mut fn_decl.ret_type));
            }
            DeclT::Typedef(td) => {
                elab.in_view_body = td.is_pointer_view;
                elab.elab_type(&env, Rc::make_mut(&mut td.body));
                elab.in_view_body = false;
            }
            DeclT::StructDefn(StructDefn { fields, .. }) => {
                let siblings = fields.clone();
                for f in fields {
                    elab.elab_field(&env, f, &siblings);
                }
            }
            DeclT::UnionDefn(UnionDefn { fields, .. }) => {
                let siblings = fields.clone();
                for f in fields {
                    elab.elab_field(&env, f, &siblings);
                }
            }
            DeclT::LetDecl(let_decl) => {
                let env = &mut env.clone();
                for arg in &mut let_decl.params {
                    elab.elab_type(env, Rc::make_mut(&mut arg.ty));
                }
                elab.elab_type(env, Rc::make_mut(&mut let_decl.ret_type));
            }
            DeclT::GlobalVar(GlobalVar { ty, .. }) => {
                elab.elab_type(&env, Rc::make_mut(ty));
            }
            DeclT::StructDecl(_) | DeclT::IncludeDecl(_) | DeclT::OpaqueTypeDecl(_) => {}
        }
        env.push_decl(decl);
    }
    // Main pass: full elaboration. Bodies and specifications can now see
    // properly elaborated signatures for every other declaration.
    for decl in &mut tu.decls {
        if let DeclT::FnDefn(FnDefn { decl: fn_decl, .. }) = &mut decl.val {
            if fn_decl.is_rec {
                // Elaborate the fn_decl's types before pre-registering so
                // recursive calls see Ref instead of Unknown pointer kinds.
                elab.elab_fn_decl(&env, fn_decl);
                env.push_fn_decl(fn_decl.clone());
            }
        }
        // Pre-register struct definitions so self-referential fields resolve
        if let DeclT::StructDefn(s) = &decl.val {
            env.push_struct(s.clone());
        }
        elab.elab_decl(&env, decl);
        env.push_decl(decl);
    }
}
