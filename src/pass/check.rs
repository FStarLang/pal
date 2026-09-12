use std::rc::Rc;

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    env::{Env, LocalDeclKind},
    ir::*,
    mayberc::MaybeRc,
};

struct Checker<'a> {
    pass: &'a str,
    check_types: bool,
    diags: &'a mut Diagnostics,
}

impl<'a> Checker<'a> {
    fn report(&mut self, msg: String, loc: &SourceInfo) {
        self.diags.report(Diagnostic {
            loc: loc.location().clone(),
            level: DiagnosticLevel::Error,
            msg: format!("(internal, after {}) {}", self.pass, msg),
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

    fn check_type_eq(&mut self, env: &Env, actual: MaybeRc<Type>, expected: MaybeRc<Type>) {
        if self.check_types && !env.vtype_eq(actual.clone(), expected.clone()) {
            self.report(
                format!("expected type {} got {}", expected, actual),
                &actual.loc,
            )
        }
    }

    fn check_has_type(&mut self, env: &Env, rval: &Expr, expected: MaybeRc<Type>) {
        if self.check_types
            && let Some(ty) = self.infer_expr(env, rval)
            && !env.vtype_eq(ty.clone().into(), expected.clone())
        {
            self.report(
                format!(
                    "expected type {}, but got {} with type {}",
                    expected, rval, ty
                ),
                &rval.loc,
            )
        }
    }

    fn check_slprop(&mut self, env: &Env, p: &Expr) {
        self.check_rvalue(env, p);
        self.check_has_type(env, p, TypeT::SLProp.with_loc_core(p.loc.clone()).into());
    }

    fn check_bool(&mut self, env: &Env, p: &Expr) {
        self.check_rvalue(env, p);
        self.check_has_type(env, p, TypeT::Bool.with_loc_core(p.loc.clone()).into());
    }

    fn check_field(&mut self, env: &Env, field: &Field, siblings: &[Field]) {
        match &field.val {
            FieldT::Plain { name, ty } => {
                // A flexible-array-member `_refines(...)` length refinement may
                // reference sibling fields (e.g. `len`) by name, so bring the
                // other fields into scope before checking the refinement.
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
                    self.check_type(env, ty);
                } else {
                    self.check_type(env, ty);
                }
            }
            FieldT::BitField { name: _, ty, .. } => self.check_type(env, ty),
        }
    }

    fn check_type(&mut self, env: &Env, ty: &Type) {
        match &ty.val {
            TypeT::Void => {}
            TypeT::Bool => {}
            TypeT::Int {
                signed: _,
                width: _,
            } => {}
            TypeT::Float { width: _ } => {}
            TypeT::SizeT => {}
            TypeT::PtrdiffT => {}
            TypeT::Pointer(ty, _kind) => {
                self.check_type(env, ty);
            }
            TypeT::FixedArray(elem_ty, _) => {
                self.check_type(env, elem_ty);
            }
            TypeT::FlexArray(elem_ty) => {
                self.check_type(env, elem_ty);
            }
            TypeT::FnPtr { args, ret, .. } => {
                for a in args {
                    self.check_type(env, a);
                }
                self.check_type(env, ret);
            }
            TypeT::SpecInt | TypeT::SpecNat => {}
            TypeT::SLProp => {}
            TypeT::TypeRef(TypeRefKind::Typedef(n)) => {
                if !env.is_known_type(&n.val) {
                    self.report(format!("unknown type {}", n), &ty.loc)
                }
            }
            TypeT::TypeRef(TypeRefKind::Struct(n)) => {
                if let None = env.lookup_struct(n) {
                    self.report(format!("unknown struct {}", n), &ty.loc)
                }
            }
            TypeT::TypeRef(TypeRefKind::Union(n)) => {
                if let None = env.lookup_union(n) {
                    self.report(format!("unknown union {}", n), &ty.loc)
                }
            }
            TypeT::Refine(ty, p) | TypeT::RefineAlways(ty, p) | TypeT::RefineUninit(ty, p) => {
                self.check_type(env, ty);
                let env = &mut env.clone();
                env.push_this(ty.clone());
                self.check_slprop(env, p);
            }
            TypeT::RefineValue(ty, binding_name, binding_ty, p) => {
                self.check_type(env, ty);
                self.check_type(env, binding_ty);
                let env = &mut env.clone();
                env.push_this(ty.clone());
                env.push_var_decl(binding_name, binding_ty.clone(), LocalDeclKind::RValue);
                self.check_slprop(env, p);
            }
            TypeT::Plain(ty) => self.check_type(env, ty),
            TypeT::Nullable(ty) => self.check_type(env, ty),
            TypeT::Unknown => {}
            TypeT::Error => {}
        }
    }

    fn is_valid_int_type(&self, env: &Env, ty: MaybeRc<Type>) -> bool {
        match &env.vtype_whnf(ty).val {
            TypeT::Void => false, // ?
            TypeT::Bool => true,
            TypeT::Int { .. } => true,
            TypeT::Float { .. } => true,
            TypeT::SizeT => true,
            TypeT::PtrdiffT => true,
            TypeT::Pointer(_, _) => true, // == 0 ?
            TypeT::FixedArray(_, _) => false,
            TypeT::FlexArray(_) => false,
            TypeT::FnPtr { .. } => true, // == 0 (null check)
            TypeT::SpecInt | TypeT::SpecNat => true,
            TypeT::SLProp => true, // true/false
            TypeT::TypeRef(_) => false,
            TypeT::Refine(..)
            | TypeT::RefineAlways(..)
            | TypeT::RefineUninit(..)
            | TypeT::RefineValue(..)
            | TypeT::Plain(..)
            | TypeT::Nullable(..) => false,
            TypeT::Unknown => true,
            TypeT::Error => true,
        }
    }

    fn check_inline_pulse_code(&mut self, env: &Env, code: &InlinePulseCode) {
        let env = &mut env.clone();
        for tok in &code.tokens {
            match tok {
                InlinePulseToken::RValueAntiquot { expr, .. }
                | InlinePulseToken::LValueAntiquot { expr, .. } => self.check_rvalue(env, expr),
                InlinePulseToken::TypeAntiquot { ty, .. } => self.check_type(env, ty),
                InlinePulseToken::Declare { ident, ty, .. } => {
                    self.check_type(env, ty);
                    env.push_var_decl(ident, ty.clone(), LocalDeclKind::RValue);
                }
                InlinePulseToken::Verbatim(_) => {}
                InlinePulseToken::FieldAntiquot { .. } => {
                    // TODO: check that field exists
                }
                InlinePulseToken::AuxFnAntiquot { .. } => {
                    // Checked at emit time
                }
            }
        }
    }

    fn check_rvalue(&mut self, env: &Env, rval: &Expr) {
        match &rval.val {
            ExprT::BoolLit(_) => {}
            ExprT::IntLit(_n, ty) => {
                self.check_type(env, ty);
                if self.check_types && !self.is_valid_int_type(env, ty.clone().into()) {
                    self.report(format!("invalid integer type: {}", ty), &rval.loc);
                }
            }
            ExprT::FloatLit(_n, ty) => {
                self.check_type(env, ty);
                if self.check_types
                    && !matches!(
                        &env.vtype_whnf(ty.clone().into()).val,
                        TypeT::Float { .. } | TypeT::Error
                    )
                {
                    self.report(format!("invalid floating literal type: {}", ty), &rval.loc);
                }
            }
            ExprT::Var(n) => self.check_var(env, n, false),
            ExprT::Deref(inner) => {
                self.check_rvalue(env, inner);
                if self.check_types
                    && let Some(rval_ty) = self.infer_expr(env, inner)
                    && !self.is_pointer_type(env, rval_ty.clone())
                {
                    self.report(format!("not a pointer type: {}", rval_ty), &inner.loc)
                }
            }
            ExprT::Member(x, a) => {
                self.check_rvalue(env, x);
                if self.check_types
                    && let Some(t) = self.infer_expr(env, x)
                {
                    let t = env.vtype_whnf(t);
                    match &t.val {
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
                self.check_rvalue(env, x);
            }
            ExprT::Index(arr, idx) => {
                self.check_rvalue(env, arr);
                self.check_rvalue(env, idx);
                if self.check_types {
                    if let Some(arr_ty) = self.infer_expr(env, arr) {
                        let arr_ty = env.vtype_whnf(arr_ty);
                        match &arr_ty.val {
                            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr) => {}
                            TypeT::FixedArray(_, _) => {}
                            TypeT::FlexArray(_) => {}
                            TypeT::Error => {}
                            _ => self.report(format!("not an array type: {}", arr_ty), &rval.loc),
                        }
                    }
                    if let Some(idx_ty) = self.infer_expr(env, idx) {
                        let idx_ty = env.vtype_whnf(idx_ty);
                        match &idx_ty.val {
                            TypeT::SizeT => {}
                            TypeT::Error => {}
                            _ => self.report(
                                format!("array index must have type SizeT, got: {}", idx_ty),
                                &idx.loc,
                            ),
                        }
                    }
                }
            }
            ExprT::Ref(lval) => {
                self.check_rvalue(env, lval);
                if !env.is_addressable(lval) {
                    self.report(format!("expected lvalue for &, got {}", lval), &rval.loc);
                }
            }
            ExprT::UnOp(un_op, arg) => {
                self.check_rvalue(env, arg);
                if self.check_types
                    && let Some(arg_ty) = self.infer_expr(env, arg)
                {
                    match un_op {
                        UnOp::Not => match &env.vtype_whnf(arg_ty.clone().into()).val {
                            TypeT::Bool | TypeT::Error => {}
                            _ => self.report(
                                format!("! needs to be applied to bool, not {}", arg_ty),
                                &rval.loc,
                            ),
                        },
                        UnOp::Neg | UnOp::BitNot => {}
                    }
                }
            }
            ExprT::BinOp(bin_op, lhs, rhs) => {
                self.check_rvalue(env, lhs);
                self.check_rvalue(env, rhs);
                if self.check_types
                    && let (Some(lhs_ty), Some(rhs_ty)) =
                        (self.infer_expr(env, lhs), self.infer_expr(env, rhs))
                {
                    let check_eq = {
                        let lhs_ty = lhs_ty.clone();
                        let rhs_ty = rhs_ty.clone();
                        move |this: &mut Checker| {
                            if !env.vtype_eq(lhs_ty.clone().into(), rhs_ty.clone().into()) {
                                this.report(
                                    format!(
                                        "binop applied to mismatching types {} and {}",
                                        lhs_ty, rhs_ty
                                    ),
                                    &rval.loc,
                                )
                            }
                        }
                    };
                    match bin_op {
                        BinOp::Eq => check_eq(self),
                        BinOp::LogAnd | BinOp::LogOr | BinOp::Implies => {
                            check_eq(self);
                            match &env.vtype_whnf(lhs_ty.clone().into()).val {
                                TypeT::Bool | TypeT::SLProp | TypeT::Error => {}
                                _ => self.report(
                                    format!(
                                        "{} needs to be applied to bool/slprop, not {}",
                                        bin_op, lhs_ty
                                    ),
                                    &rval.loc,
                                ),
                            }
                        }
                        BinOp::LEq
                        | BinOp::Lt
                        | BinOp::Mul
                        | BinOp::Div
                        | BinOp::Mod
                        | BinOp::Add
                        | BinOp::Sub
                        | BinOp::BitAnd
                        | BinOp::BitOr
                        | BinOp::BitXor => {
                            // Allow pointer arithmetic: array/arrayptr ± integer
                            let lhs_w = env.vtype_whnf(lhs_ty.clone().into());
                            let rhs_w = env.vtype_whnf(rhs_ty.clone().into());
                            let is_ptr_arith = matches!(bin_op, BinOp::Add | BinOp::Sub)
                                && (matches!(
                                    &lhs_w.val,
                                    TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                                ) || matches!(
                                    &rhs_w.val,
                                    TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                                ));
                            if !is_ptr_arith {
                                check_eq(self)
                            }
                        }
                        BinOp::Shl | BinOp::Shr => {
                            let u32_ty: MaybeRc<Type> = TypeT::Int {
                                signed: false,
                                width: 32,
                            }
                            .with_loc(rhs.loc.clone())
                            .into();
                            if !env.vtype_eq(rhs_ty.clone().into(), u32_ty) {
                                self.report(
                                    format!("shift amount must be uint32_t, not {}", rhs_ty),
                                    &rval.loc,
                                )
                            }
                        }
                    }
                }
            }
            ExprT::FnCall(f, args) => {
                for arg in args {
                    self.check_rvalue(env, arg)
                }
                let Some(fn_decl) = env.lookup_fn(f) else {
                    self.report(format!("unknown function {}", f.val), &rval.loc);
                    return;
                };
                if fn_decl.args.len() != args.len() {
                    self.report(
                        format!(
                            "incorrect number of arguments, expected {}, got {}",
                            fn_decl.args.len(),
                            args.len()
                        ),
                        &rval.loc,
                    );
                }
                for (decl_arg, arg) in fn_decl.args.iter().zip(args.iter()) {
                    self.check_has_type(env, arg, decl_arg.ty.clone().into());
                }
            }
            ExprT::FnRef(f) => {
                if env.lookup_fn(f).is_none() {
                    self.report(format!("unknown function {}", f.val), &rval.loc);
                }
            }
            ExprT::FnPtrCall(f, args) => {
                self.check_rvalue(env, f);
                for arg in args {
                    self.check_rvalue(env, arg)
                }
            }
            ExprT::Cast(rval, ty) => {
                self.check_rvalue(env, rval);
                self.check_type(env, ty);
            }
            ExprT::InlinePulse(code, ty) => {
                self.check_type(env, ty);
                self.check_inline_pulse_code(env, code);
            }
            ExprT::Live(lval) => self.check_rvalue(env, lval),
            ExprT::Old(rval) => self.check_rvalue(env, rval),
            ExprT::Forall(var, ty, body) | ExprT::Exists(var, ty, body) => {
                self.check_type(env, ty);
                let mut env = env.clone();
                env.push_var_decl(var, ty.clone(), LocalDeclKind::RValue);
                self.check_rvalue(&env, body);
            }
            ExprT::StructInit(name, fields) => {
                let Some(s) = env.lookup_struct(name) else {
                    self.report(format!("unknown struct {}", name), &rval.loc);
                    return;
                };
                if self.check_types {
                    // Fields may be omitted (e.g. a flexible array member, or a
                    // partial designated initializer); omitted fields are filled
                    // with their default by the emitter. Only reject supplying
                    // more fields than the struct declares.
                    if fields.len() > s.fields.len() {
                        self.report(
                            format!(
                                "struct {} has {} fields, but {} were given",
                                name,
                                s.fields.len(),
                                fields.len()
                            ),
                            &rval.loc,
                        );
                    }
                    for (fld_name, fld_val) in fields {
                        self.check_rvalue(env, fld_val);
                        let Some(fld_ty) = s.get_field(fld_name) else {
                            self.report(
                                format!("no field {} in struct {}", fld_name, name),
                                &rval.loc,
                            );
                            continue;
                        };
                        self.check_has_type(env, fld_val, fld_ty.clone().into());
                    }
                }
            }
            ExprT::UnionInit(name, fld_name, fld_val) => {
                let Some(u) = env.lookup_union(name) else {
                    self.report(format!("unknown union {}", name), &rval.loc);
                    return;
                };
                if self.check_types {
                    self.check_rvalue(env, fld_val);
                    let Some(fld_ty) = u.get_field(fld_name) else {
                        self.report(
                            format!("no field {} in union {}", fld_name, name),
                            &rval.loc,
                        );
                        return;
                    };
                    self.check_has_type(env, fld_val, fld_ty.clone().into());
                }
            }
            ExprT::Malloc(ty) | ExprT::Calloc(ty) => self.check_type(env, ty),
            ExprT::ArrayInit { elem_ty, elems, .. } => {
                self.check_type(env, elem_ty);
                for elem in elems {
                    self.check_rvalue(env, elem);
                }
            }
            ExprT::MallocArray(ty, count) | ExprT::CallocArray(ty, count) => {
                self.check_type(env, ty);
                self.check_rvalue(env, count);
            }
            ExprT::MallocFlex(ty, count) | ExprT::CallocFlex(ty, count) => {
                self.check_type(env, ty);
                self.check_rvalue(env, count);
            }
            ExprT::Memset(ty, ptr, value, count) => {
                self.check_type(env, ty);
                self.check_rvalue(env, ptr);
                self.check_rvalue(env, value);
                self.check_rvalue(env, count);
            }
            ExprT::MemsetZero(ty, ptr) => {
                self.check_type(env, ty);
                self.check_rvalue(env, ptr);
            }
            ExprT::Free(val) => self.check_rvalue(env, val),
            ExprT::ContainerOf(ptr, struct_ty, field) => {
                self.check_rvalue(env, ptr);
                self.check_type(env, struct_ty);
                if self.check_types {
                    match &env.vtype_whnf(struct_ty.clone().into()).val {
                        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
                            let Some(s) = env.lookup_struct(n) else {
                                return self.report(format!("unknown structure {}", n), &rval.loc);
                            };
                            if s.get_field(field).is_none() {
                                return self.report(
                                    format!("no field {} in structure {}", field, n),
                                    &rval.loc,
                                );
                            }
                        }
                        t => {
                            return self.report(
                                format!("_container_of expects a struct type, got {}", t),
                                &struct_ty.loc,
                            );
                        }
                    }
                }
            }
            ExprT::PreIncr(val)
            | ExprT::PostIncr(val)
            | ExprT::PreDecr(val)
            | ExprT::PostDecr(val) => self.check_lvalue(env, val),
            ExprT::Cond(cond, then_expr, else_expr) => {
                self.check_rvalue(env, cond);
                self.check_rvalue(env, then_expr);
                self.check_rvalue(env, else_expr);
            }
            ExprT::AssignExpr(lhs, rhs) => {
                self.check_rvalue(env, lhs);
                self.check_rvalue(env, rhs);
                if self.check_types
                    && let (Some(lhs_ty), Some(rhs_ty)) =
                        (self.infer_expr(env, lhs), self.infer_expr(env, rhs))
                {
                    self.check_type_eq(env, rhs_ty.into(), lhs_ty.into());
                }
            }
            ExprT::SizeOf(ty) | ExprT::AlignOf(ty) => self.check_type(env, ty),
            ExprT::Error(ty) => self.check_type(env, ty),
        }
    }

    fn is_pointer_type(&mut self, env: &Env, ty: MaybeRc<Type>) -> bool {
        match &env.vtype_whnf(ty).val {
            TypeT::Pointer(_ty, _kind) => true,
            TypeT::Error => true,
            _ => false,
        }
    }

    fn check_lvalue(&mut self, env: &Env, lval: &Expr) {
        self.check_rvalue(env, lval);
        if !env.is_lvalue(lval) {
            self.report(format!("expected lvalue, got {}", lval), &lval.loc);
        }
    }

    fn check_var(&mut self, env: &Env, n: &Ident, needs_lvalue: bool) {
        match env.lookup_var(n) {
            None => match env.lookup_global_var(n) {
                Some(_) => {
                    if needs_lvalue {
                        self.report(
                            format!("need lvalue, but global {} is rvalue", n.val),
                            &n.loc,
                        );
                    }
                }
                None => self.report(format!("unknown local variable {}", n.val), &n.loc),
            },
            Some(ldecl) => {
                if ldecl.kind == LocalDeclKind::RValue && needs_lvalue {
                    self.report(format!("need lvalue, but {} is rvalue", n.val), &n.loc);
                }
            }
        }
    }

    fn check_stmt(&mut self, env: &Env, stmt: &Stmt) {
        match &stmt.val {
            StmtT::Call(rval) => self.check_rvalue(env, rval),
            StmtT::Decl(_, ty) => self.check_type(env, ty),
            StmtT::Let(_, ty, value) => {
                self.check_type(env, ty);
                self.check_rvalue(env, value);
                if self.check_types
                    && let Some(value_ty) = self.infer_expr(env, value)
                {
                    self.check_type_eq(env, value_ty.into(), ty.clone().into());
                }
            }
            StmtT::DeclStackArray {
                elem_type, size, ..
            } => {
                self.check_type(env, elem_type);
                self.check_rvalue(env, size);
            }
            StmtT::Assign(x, v) => {
                self.check_lvalue(env, x);
                self.check_rvalue(env, v);
                if self.check_types
                    && let (Some(x_ty), Some(v_ty)) =
                        (self.infer_expr(env, x), self.infer_expr(env, v))
                {
                    self.check_type_eq(env, v_ty.into(), x_ty.into());
                }
            }
            StmtT::If {
                cond,
                then_branch,
                else_branch,
                ensures,
            } => {
                self.check_bool(env, cond);
                for e in &**ensures {
                    self.check_slprop(env, e)
                }
                self.check_stmts(env, then_branch);
                self.check_stmts(env, else_branch);
            }
            StmtT::Match {
                scrutinee,
                branches,
                default_branch,
                ensures,
            } => {
                self.check_rvalue(env, scrutinee);
                let scrutinee_ty = self.infer_expr(env, scrutinee);
                for branch in &**branches {
                    for pattern in &*branch.patterns {
                        self.check_rvalue(env, pattern);
                        if self.check_types
                            && let (Some(scrutinee_ty), Some(pattern_ty)) =
                                (scrutinee_ty.clone(), self.infer_expr(env, pattern))
                        {
                            self.check_type_eq(env, pattern_ty.into(), scrutinee_ty.into());
                        }
                    }
                    self.check_stmts(env, &branch.body);
                }
                self.check_stmts(env, default_branch);
                for e in &**ensures {
                    self.check_slprop(env, e);
                }
            }
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => {
                self.check_bool(env, cond);
                for inv in &**inv {
                    self.check_slprop(env, inv)
                }
                for r in &**requires {
                    self.check_bool(env, r)
                }
                for e in &**ensures {
                    self.check_bool(env, e)
                }
                let mut loop_env = env.clone();
                loop_env.enter_loop();
                self.check_stmts(&loop_env, body);
            }
            StmtT::Break | StmtT::Continue => {
                if !env.in_loop() {
                    self.report(
                        format!(
                            "{} outside of loop",
                            if matches!(&stmt.val, StmtT::Break) {
                                "break"
                            } else {
                                "continue"
                            }
                        ),
                        &stmt.loc,
                    );
                }
            }
            StmtT::Return(v) => {
                if let Some(v) = v {
                    self.check_rvalue(env, v);
                    if self.check_types
                        && let Some(ret_ty) = &env.return_type
                    {
                        self.check_has_type(env, v, ret_ty.clone().into());
                    }
                }
            }
            StmtT::Assert(v) => self.check_slprop(env, v),
            StmtT::GhostStmt(code) => self.check_inline_pulse_code(env, code),
            StmtT::Goto(_) => {}
            StmtT::Label { ensures, .. } => {
                for e in &**ensures {
                    self.check_slprop(env, e)
                }
            }
            StmtT::GotoBlock {
                body,
                label: _,
                ensures,
            } => {
                self.check_stmts(env, body);
                for e in &**ensures {
                    self.check_slprop(env, e)
                }
            }
            StmtT::Error => {}
        }
    }

    fn check_stmts(&mut self, env: &Env, stmts: &Vec<Rc<Stmt>>) {
        let env = &mut env.clone();
        for stmt in stmts {
            self.check_stmt(env, stmt);
            env.push_stmt(stmt);
        }
    }

    fn check_slprops(&mut self, env: &Env, slprops: &Vec<Rc<Expr>>) {
        for p in slprops {
            self.check_slprop(env, p)
        }
    }

    fn check_fn_decl(
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
        }: &FnDecl,
    ) {
        let env = &mut env.clone();
        for ga in ghost_args {
            self.check_type(env, &ga.ty);
            env.push_var_decl(&ga.name, ga.ty.clone(), LocalDeclKind::RValue);
        }
        for arg in args {
            self.check_type(env, &arg.ty);
            env.push_arg(arg, LocalDeclKind::RValue);
        }
        self.check_slprops(env, requires);
        self.check_type(env, ret_type);
        env.push_return(ret_type.clone());
        self.check_slprops(env, ensures);
        if let Some(dec) = decreases {
            self.check_rvalue(env, dec);
        }
    }

    fn check_decl(&mut self, env: &Env, decl: &Decl) {
        // TODO: check double definition
        match &decl.val {
            DeclT::FnDefn(FnDefn { decl, body }) => {
                self.check_fn_decl(env, decl);
                let env = &mut env.clone();
                env.push_fn_decl_args_for_body(decl);
                self.check_stmts(env, body);
            }
            DeclT::FnDecl(fn_decl) => self.check_fn_decl(env, fn_decl),
            DeclT::Typedef(TypeDefn {
                name: _,
                body,
                is_pointer_view: _,
            }) => self.check_type(env, body),
            DeclT::StructDefn(StructDefn {
                name: _,
                refines,
                fields,
                ..
            }) => {
                self.check_type(env, refines);
                for f in fields {
                    self.check_field(env, f, fields);
                }
            }
            DeclT::StructDecl(_) => {}
            DeclT::UnionDefn(UnionDefn {
                name: _,
                fields,
                abi_size: _,
            }) => {
                for f in fields {
                    self.check_field(env, f, fields);
                }
            }
            DeclT::IncludeDecl(_) => {}
            DeclT::OpaqueTypeDecl(decl) => {
                let env = &mut env.clone();
                self.check_inline_pulse_code(env, &decl.code);
            }
            DeclT::LetDecl(LetDecl {
                name: _,
                is_rec: _,
                is_impure: _,
                ret_type,
                params,
                requires,
                ensures,
                body,
            }) => {
                self.check_type(env, ret_type);
                for arg in params {
                    self.check_type(env, &arg.ty);
                }
                let env = &mut env.clone();
                for arg in params {
                    env.push_arg(arg, LocalDeclKind::LValue);
                }
                for r in requires {
                    self.check_rvalue(env, r);
                }
                for e in ensures {
                    self.check_rvalue(env, e);
                }
                self.check_rvalue(env, body);
            }
            DeclT::GlobalVar(GlobalVar {
                name: _,
                ty,
                init,
                is_pure: _,
                is_extern: _,
                opaque_to_smt: _,
                is_enum_constant: _,
            }) => {
                self.check_type(env, ty);
                if let Some(init) = init {
                    self.check_rvalue(env, init);
                }
            }
        }
    }

    fn check_translation_unit(&mut self, tu: &TranslationUnit) {
        let mut env = Env::new();
        // Pre-register every declaration so checking is order-independent.
        for decl in &tu.decls {
            env.push_decl(decl);
        }
        for decl in &tu.decls {
            if let DeclT::FnDefn(FnDefn { decl: fn_decl, .. }) = &decl.val {
                if fn_decl.is_rec {
                    env.push_fn_decl(fn_decl.clone());
                }
            }
            // Pre-register struct definitions so self-referential fields resolve
            if let DeclT::StructDefn(s) = &decl.val {
                env.push_struct(s.clone());
            }
            self.check_decl(&env, decl);
            env.push_decl(decl);
        }
    }
}

pub fn check(diags: &mut Diagnostics, tu: &mut TranslationUnit, pass: &str, check_types: bool) {
    Checker {
        pass,
        check_types,
        diags,
    }
    .check_translation_unit(tu);
}
