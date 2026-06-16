use num_bigint::BigInt;

use crate::diag::{Diagnostic, DiagnosticLevel, Diagnostics};
use crate::env::{Env, LocalDeclKind};
use crate::ir::*;
use crate::mayberc::MaybeRc;
use std::rc::Rc;

struct Elaborator<'a> {
    diags: &'a mut Diagnostics,
}

fn cast_to(rval: &mut Rc<Expr>, ty: Rc<Type>) {
    *rval = ExprT::Cast(rval.clone(), ty).with_loc(rval.loc.clone())
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

    fn elab_field(&mut self, env: &Env, field: &mut Field) {
        match &mut field.val {
            FieldT::Plain { name: _, ty } => self.elab_type(env, Rc::make_mut(ty)),
        }
    }

    fn elab_type(&mut self, env: &Env, ty: &mut Type) {
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
                }
            }
            TypeT::FixedArray(elem_ty, _) => {
                self.elab_type(env, Rc::make_mut(elem_ty));
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
            TypeT::Plain(ty) => self.elab_type(env, Rc::make_mut(ty)),
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
                    let t = env.vtype_whnf(t);
                    match &t.val {
                        // Convert _length on array → VAttr::Length
                        TypeT::Pointer(_, PointerKind::Array) if &*a.val == "_length" => {
                            rval.val = ExprT::VAttr(VAttr::Length, x.clone());
                        }
                        TypeT::FixedArray(_, _) if &*a.val == "_length" => {
                            rval.val = ExprT::VAttr(VAttr::Length, x.clone());
                        }
                        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
                            let Some(s) = env.lookup_struct(n) else {
                                return self.report(format!("unknown structure {}", n), &rval.loc);
                            };
                            let Some(_f) = s.get_field(a) else {
                                return self.report(
                                    format!("no field {} in structure {}", a, n),
                                    &rval.loc,
                                );
                            };
                        }
                        TypeT::TypeRef(TypeRefKind::Union(n)) => {
                            let Some(u) = env.lookup_union(n) else {
                                return self.report(format!("unknown union {}", n), &rval.loc);
                            };
                            let Some(_f) = u.get_field(a) else {
                                return self
                                    .report(format!("no field {} in union {}", a, n), &rval.loc);
                            };
                        }
                        _ => {
                            return self.report(format!("not a structure type: {}", t), &rval.loc);
                        }
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
                    let arr_is_array_ptr = env
                        .infer_expr(arr)
                        .ok()
                        .map(|t| env.vtype_whnf(t))
                        .is_some_and(|t| {
                            matches!(
                                &t.val,
                                TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                            )
                        });
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
            ExprT::Free(val) => self.elab_rvalue(env, Rc::make_mut(val), None),
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
            ExprT::ArrayInit(_, elems) => {
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
            if *rhs_kind == PointerKind::Unknown {
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
            DeclT::Typedef(typedef) => self.elab_type(env, Rc::make_mut(&mut typedef.body)),
            DeclT::StructDefn(StructDefn {
                name: _, fields, ..
            }) => {
                for f in fields {
                    self.elab_field(env, f);
                }
            }
            DeclT::StructDecl(_) => {}
            DeclT::UnionDefn(UnionDefn { name: _, fields }) => {
                for f in fields {
                    self.elab_field(env, f);
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

pub fn elab(diags: &mut Diagnostics, tu: &mut TranslationUnit) {
    let mut env = Env::new();
    let mut elab = Elaborator { diags };
    // Pre-register every declaration so that elaboration is order-independent
    // (e.g. an `_include_pulse` block in one file can refer to a typedef
    // declared in another file, and a function body can call another function
    // defined later in the translation unit). Elaboration of each decl below
    // pushes the elaborated version into the environment, overwriting this
    // initial entry.
    for decl in tu.decls.iter() {
        env.push_decl(decl);
    }
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
                elab.elab_type(&env, Rc::make_mut(&mut td.body));
            }
            DeclT::StructDefn(StructDefn { fields, .. }) => {
                for f in fields {
                    elab.elab_field(&env, f);
                }
            }
            DeclT::UnionDefn(UnionDefn { fields, .. }) => {
                for f in fields {
                    elab.elab_field(&env, f);
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
