use crate::impl_display_using_prettyir;
use crate::{ir::pretty::PrettyIR, ir::*, mayberc::MaybeRc};
use std::{collections::HashMap, collections::HashSet, rc::Rc};

#[derive(Clone, Debug, Default)]
struct Globals {
    fns: HashMap<Rc<str>, FnDecl>,
    typedefs: HashMap<Rc<str>, TypeDefn>,
    opaque_types: HashSet<Rc<str>>,
    structs: HashMap<Rc<str>, StructDefn>,
    unions: HashMap<Rc<str>, UnionDefn>,
    vars: HashMap<Rc<str>, GlobalVar>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum LocalDeclKind {
    LValue,
    RValue,
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub ty: Rc<Type>,
    pub kind: LocalDeclKind,
}

#[derive(Clone, Debug, Default)]
pub struct Env {
    globals: Rc<Globals>,
    locals: HashMap<Rc<str>, LocalDecl>,
    pub loop_depth: usize,
    pub return_type: Option<Rc<Type>>,
}

macro_rules! either_side {
    ($t:pat) => {
        ($t, _) | (_, $t)
    };
}
macro_rules! both_sides {
    ($t:pat) => {
        ($t, $t)
    };
}

#[derive(Debug, Clone)]
pub enum InferError {
    CannotDeref(MaybeRc<Type>),
    CannotAccessMember(MaybeRc<Type>),
    VariableNotFound(Rc<Ident>),
    NotAField(Rc<Ident>, Rc<Ident>),
    NotAFunction(Rc<Ident>),
    CannotIndex(MaybeRc<Type>),
}

impl_display_using_prettyir!(InferError);
impl PrettyIR for InferError {
    fn to_doc(&self) -> ::pretty::RcDoc<'_, ()> {
        use ::pretty::*;
        (match self {
            InferError::CannotDeref(ty) => docs![
                &RcAllocator,
                "cannot dereference",
                RcDoc::line(),
                ty.to_doc(),
            ],
            InferError::CannotAccessMember(ty) => docs![
                &RcAllocator,
                ty.to_doc(),
                RcDoc::line(),
                "has no members (not a structure)",
            ],
            InferError::VariableNotFound(name) => docs![
                &RcAllocator,
                "variable",
                RcDoc::line(),
                name.to_doc(),
                RcDoc::line(),
                "not found",
            ],
            InferError::NotAField(struct_name, field_name) => docs![
                &RcAllocator,
                struct_name.to_doc(),
                RcDoc::line(),
                "does not have a field",
                RcDoc::line(),
                field_name.to_doc(),
            ],
            InferError::NotAFunction(name) => docs![
                &RcAllocator,
                name.to_doc(),
                RcDoc::line(),
                "is not a function",
            ],
            InferError::CannotIndex(ty) => docs![
                &RcAllocator,
                "cannot index into",
                RcDoc::line(),
                ty.to_doc(),
            ],
        })
        .group()
        .nest(2)
        .into_doc()
    }
}

impl Env {
    pub fn new() -> Env {
        Env::default()
    }

    pub fn in_loop(&self) -> bool {
        self.loop_depth > 0
    }

    pub fn enter_loop(&mut self) {
        self.loop_depth += 1;
    }

    pub fn set_return_type(&mut self, ty: Rc<Type>) {
        self.return_type = Some(ty);
    }

    pub fn push_fn_decl(&mut self, decl: FnDecl) {
        Rc::make_mut(&mut self.globals)
            .fns
            .insert(decl.name.val.clone(), decl);
    }

    pub fn push_typedef(&mut self, defn: TypeDefn) {
        Rc::make_mut(&mut self.globals)
            .typedefs
            .insert(defn.name.val.clone(), defn);
    }

    pub fn push_opaque_type(&mut self, name: Rc<str>) {
        Rc::make_mut(&mut self.globals).opaque_types.insert(name);
    }

    pub fn is_known_type(&self, name: &str) -> bool {
        self.globals.typedefs.contains_key(name) || self.globals.opaque_types.contains(name)
    }

    pub fn push_struct(&mut self, decl: StructDefn) {
        Rc::make_mut(&mut self.globals)
            .structs
            .insert(decl.name.val.clone(), decl);
    }

    pub fn push_union(&mut self, decl: UnionDefn) {
        Rc::make_mut(&mut self.globals)
            .unions
            .insert(decl.name.val.clone(), decl);
    }

    pub fn push_global_var(&mut self, gv: GlobalVar) {
        Rc::make_mut(&mut self.globals)
            .vars
            .insert(gv.name.val.clone(), gv);
    }

    pub fn push_decl(&mut self, decl: &Decl) {
        match &decl.val {
            DeclT::FnDefn(fn_defn) => self.push_fn_decl(fn_defn.decl.clone()),
            DeclT::FnDecl(fn_decl) => self.push_fn_decl(fn_decl.clone()),
            DeclT::Typedef(defn) => self.push_typedef(defn.clone()),
            DeclT::StructDefn(struct_defn) => self.push_struct(struct_defn.clone()),
            DeclT::StructDecl(name) => {
                if !self.globals.structs.contains_key(&name.val) {
                    self.push_struct(StructDefn {
                        name: name.clone(),
                        fields: vec![],
                        eager_unfold_pred: false,
                    });
                }
            }
            DeclT::UnionDefn(union_defn) => self.push_union(union_defn.clone()),
            DeclT::IncludeDecl(_) => {}
            DeclT::LetDecl(let_decl) => {
                // Register as a function so it can be called in specs
                self.push_fn_decl(FnDecl {
                    name: let_decl.name.clone(),
                    ret_type: let_decl.ret_type.clone(),
                    args: let_decl.params.clone(),
                    ghost_args: vec![],
                    requires: let_decl.requires.clone(),
                    ensures: let_decl.ensures.clone(),
                    is_pure: !let_decl.is_impure,
                    is_rec: let_decl.is_rec,
                    decreases: None,
                });
            }
            DeclT::GlobalVar(gv) => self.push_global_var(gv.clone()),
            DeclT::OpaqueTypeDecl(decl) => {
                self.push_opaque_type(decl.name.val.clone());
            }
        }
    }

    pub fn push_var_decl(&mut self, ident: &Ident, ty: Rc<Type>, is_rvalue: LocalDeclKind) {
        self.locals.insert(
            ident.val.clone(),
            LocalDecl {
                ty,
                kind: is_rvalue,
            },
        );
    }

    pub fn push_arg(&mut self, arg: &FnArg, is_rvalue: LocalDeclKind) {
        if let Some(n) = &arg.name {
            self.push_var_decl(n, arg.ty.clone(), is_rvalue)
        }
    }

    pub fn push_fn_decl_args_for_body(&mut self, decl: &FnDecl) {
        for ga in &decl.ghost_args {
            self.push_var_decl(&ga.name, ga.ty.clone(), LocalDeclKind::RValue);
        }
        for arg in &decl.args {
            self.push_arg(arg, LocalDeclKind::LValue);
        }
        self.set_return_type(decl.ret_type.clone());
        // Make `$(return)` resolvable inside the body: a trailing ghost
        // statement after the final `return e` may reference the returned
        // value (see Emitter::emit_fn_body_stmts).
        self.push_return(decl.ret_type.clone());
    }

    pub fn lookup_fn(&self, ident: &Ident) -> Option<&FnDecl> {
        self.globals.fns.get(&ident.val)
    }

    pub fn lookup_type(&self, ident: &Ident) -> Option<&TypeDefn> {
        self.globals.typedefs.get(&ident.val)
    }

    pub fn lookup_struct(&self, ident: &Ident) -> Option<&StructDefn> {
        self.globals.structs.get(&ident.val)
    }

    pub fn lookup_union(&self, ident: &Ident) -> Option<&UnionDefn> {
        self.globals.unions.get(&ident.val)
    }

    pub fn lookup_var(&self, ident: &Ident) -> Option<&LocalDecl> {
        self.locals.get(&ident.val)
    }

    pub fn lookup_global_var(&self, ident: &Ident) -> Option<&GlobalVar> {
        self.globals.vars.get(&ident.val)
    }

    pub fn lookup_var_type(&self, ident: &Ident) -> Option<&Rc<Type>> {
        self.lookup_var(ident)
            .map(|decl| &decl.ty)
            .or_else(|| self.lookup_global_var(ident).map(|gv| &gv.ty))
    }

    pub fn push_stmt(&mut self, stmt: &Stmt) {
        match &stmt.val {
            StmtT::Decl(ident, ty) => self.push_var_decl(ident, ty.clone(), LocalDeclKind::LValue),
            StmtT::DeclStackArray {
                name, elem_type, ..
            } => {
                let array_ty = TypeT::Pointer(elem_type.clone(), PointerKind::Array)
                    .with_loc(name.loc.clone());
                self.push_var_decl(name, array_ty, LocalDeclKind::LValue);
            }
            _ => {}
        }
    }

    pub fn push_this(&mut self, ty: Rc<Type>) -> Rc<IdentT> {
        let id: Rc<IdentT> = Rc::from("this");
        self.locals.insert(
            id.clone(),
            LocalDecl {
                ty,
                kind: LocalDeclKind::RValue,
            },
        );
        id
    }

    pub fn push_return(&mut self, ty: Rc<Type>) -> Rc<IdentT> {
        let id: Rc<IdentT> = Rc::from("return");
        self.locals.insert(
            id.clone(),
            LocalDecl {
                ty,
                kind: LocalDeclKind::RValue,
            },
        );
        id
    }

    pub fn infer_expr(&self, expr: &Expr) -> Result<MaybeRc<Type>, InferError> {
        match &expr.val {
            ExprT::Var(ident) => {
                let Some(var_type) = self.lookup_var_type(ident) else {
                    return Err(InferError::VariableNotFound(ident.clone()));
                };
                Ok(var_type.clone().into())
            }
            ExprT::Deref(x) => {
                let x_ty = self.vtype_whnf(self.infer_expr(x)?);
                match &x_ty.val {
                    TypeT::Pointer(to, _) => Ok(to.clone().into()),
                    _ => Err(InferError::CannotDeref(x_ty)),
                }
            }
            ExprT::Member(x, a) => {
                let x_ty = self.vtype_whnf(self.infer_expr(x)?);
                match &x_ty.val {
                    TypeT::TypeRef(TypeRefKind::Struct(s_name)) => {
                        let Some(s) = self.lookup_struct(s_name) else {
                            return Err(InferError::CannotAccessMember(x_ty.clone()));
                        };
                        let Some(f) = s.get_field(a) else {
                            return Err(InferError::NotAField(s_name.clone(), a.clone()));
                        };
                        Ok(f.clone().into())
                    }
                    TypeT::TypeRef(TypeRefKind::Union(u_name)) => {
                        let Some(u) = self.lookup_union(u_name) else {
                            return Err(InferError::CannotAccessMember(x_ty.clone()));
                        };
                        let Some(f) = u.get_field(a) else {
                            return Err(InferError::NotAField(u_name.clone(), a.clone()));
                        };
                        Ok(f.clone().into())
                    }
                    _ => Err(InferError::CannotAccessMember(x_ty)),
                }
            }
            ExprT::VAttr(VAttr::Length, _) => {
                Ok(TypeT::SpecInt.with_loc_core(expr.loc.clone()).into())
            }
            ExprT::VAttr(VAttr::Active(_), _) => {
                Ok(TypeT::Bool.with_loc_core(expr.loc.clone()).into())
            }
            ExprT::Index(arr, _idx) => {
                let arr_ty = self.vtype_whnf(self.infer_expr(arr)?);
                match &arr_ty.val {
                    TypeT::Pointer(elem, PointerKind::Array | PointerKind::ArrayPtr) => {
                        Ok(elem.clone().into())
                    }
                    TypeT::FixedArray(elem, _) => Ok(elem.clone().into()),
                    _ => Err(InferError::CannotIndex(arr_ty)),
                }
            }
            ExprT::IntLit(_, ty) => Ok(ty.clone().into()),
            ExprT::FloatLit(_, ty) => Ok(ty.clone().into()),
            ExprT::Ref(v) => Ok(expr
                .reuse_loc(TypeT::Pointer(
                    self.infer_expr(v)?.to_rc(),
                    PointerKind::Ref,
                ))
                .into()),
            ExprT::FnCall(f, _args) => match self.globals.fns.get(&f.val) {
                Some(f_decl) => Ok(f_decl.ret_type.clone().into()),
                None => Err(InferError::NotAFunction(f.clone())),
            },
            ExprT::Cast(_, ty) => Ok(ty.clone().into()),
            ExprT::Error(ty) => Ok(ty.clone().into()),
            ExprT::SizeOf(_) | ExprT::AlignOf(_) => Ok(expr.reuse_loc(TypeT::SizeT).into()),
            ExprT::Malloc(ty) | ExprT::Calloc(ty) => Ok(expr
                .reuse_loc(TypeT::Pointer(ty.clone(), PointerKind::Ref))
                .into()),
            ExprT::MallocArray(ty, _) | ExprT::CallocArray(ty, _) => Ok(expr
                .reuse_loc(TypeT::Pointer(ty.clone(), PointerKind::Array))
                .into()),
            ExprT::Free(_) => Ok(TypeT::Void.with_loc_core(expr.loc.clone()).into()),
            ExprT::Memset(_, _, _, _) => Ok(TypeT::Void.with_loc_core(expr.loc.clone()).into()),
            ExprT::MemsetZero(_, _) => Ok(TypeT::Void.with_loc_core(expr.loc.clone()).into()),
            ExprT::PreIncr(val)
            | ExprT::PostIncr(val)
            | ExprT::PreDecr(val)
            | ExprT::PostDecr(val) => self.infer_expr(val),
            ExprT::InlinePulse(_, ty) => Ok(ty.clone().into()),
            ExprT::UnOp(UnOp::Not, _) | ExprT::BinOp(BinOp::Eq | BinOp::LEq | BinOp::Lt, _, _) => {
                Ok(TypeT::Bool.with_loc_core(expr.loc.clone()).into())
            }
            ExprT::UnOp(UnOp::Neg | UnOp::BitNot, lhs)
            | ExprT::BinOp(
                BinOp::LogAnd
                | BinOp::LogOr
                | BinOp::Implies
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Shl
                | BinOp::Shr,
                lhs,
                _,
            ) => self.infer_expr(lhs),
            ExprT::BinOp(BinOp::Add, lhs, rhs) => {
                let lhs_ty = self.vtype_whnf(self.infer_expr(lhs)?);
                let rhs_ty = self.vtype_whnf(self.infer_expr(rhs)?);
                // pointer + int → arrayptr
                match (&lhs_ty.val, &rhs_ty.val) {
                    (TypeT::Pointer(elem, PointerKind::Array | PointerKind::ArrayPtr), _) => {
                        Ok(expr
                            .reuse_loc(TypeT::Pointer(elem.clone(), PointerKind::ArrayPtr))
                            .into())
                    }
                    (_, TypeT::Pointer(elem, PointerKind::Array | PointerKind::ArrayPtr)) => {
                        Ok(expr
                            .reuse_loc(TypeT::Pointer(elem.clone(), PointerKind::ArrayPtr))
                            .into())
                    }
                    _ => Ok(lhs_ty),
                }
            }
            ExprT::BinOp(BinOp::Sub, lhs, rhs) => {
                let lhs_ty = self.vtype_whnf(self.infer_expr(lhs)?);
                let rhs_ty = self.vtype_whnf(self.infer_expr(rhs)?);
                // pointer - pointer → PtrdiffT
                match (&lhs_ty.val, &rhs_ty.val) {
                    (
                        TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr),
                        TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr),
                    ) => Ok(TypeT::PtrdiffT.with_loc_core(expr.loc.clone()).into()),
                    _ => Ok(lhs_ty),
                }
            }
            ExprT::BoolLit(_) => Ok(TypeT::Bool.with_loc_core(expr.loc.clone()).into()),
            ExprT::Live(_) => Ok(TypeT::SLProp.with_loc_core(expr.loc.clone()).into()),
            ExprT::Old(v) => self.infer_expr(v),
            ExprT::Forall(var, ty, body) | ExprT::Exists(var, ty, body) => {
                let mut env = self.clone();
                env.push_var_decl(var, ty.clone(), LocalDeclKind::RValue);
                env.infer_expr(body)
            }
            ExprT::StructInit(name, _) => Ok(expr
                .reuse_loc(TypeT::TypeRef(TypeRefKind::Struct(name.clone())))
                .into()),
            ExprT::UnionInit(name, _, _) => Ok(expr
                .reuse_loc(TypeT::TypeRef(TypeRefKind::Union(name.clone())))
                .into()),
            ExprT::ArrayInit(elem_ty, elems) => Ok(expr
                .reuse_loc(TypeT::FixedArray(elem_ty.clone(), elems.len() as u64))
                .into()),
            ExprT::Cond(_, then_expr, _) => self.infer_expr(then_expr),
            ExprT::AssignExpr(_, rhs) => self.infer_expr(rhs),
        }
    }

    pub fn meet_type(&self, a: MaybeRc<Type>, b: MaybeRc<Type>) -> Option<MaybeRc<Type>> {
        let a0 = a.clone();
        let b0 = b.clone();
        let a = self.vtype_whnf(a);
        let b = self.vtype_whnf(b);
        if self.vtype_eq(a.clone(), b.clone()) {
            return Some(a0);
        }
        match (&a.val, &b.val) {
            (_, TypeT::Error | TypeT::Unknown) => Some(b0),
            (TypeT::Error | TypeT::Unknown, _) => Some(a0),

            (
                TypeT::SpecInt | TypeT::SpecNat,
                TypeT::Bool | TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT,
            ) => Some(a0),
            (
                TypeT::Bool | TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT,
                TypeT::SpecInt | TypeT::SpecNat,
            ) => Some(b0),

            (TypeT::SizeT, TypeT::Bool | TypeT::Int { .. }) => Some(a0),
            (TypeT::Bool | TypeT::Int { .. }, TypeT::SizeT) => Some(b0),

            (TypeT::PtrdiffT, TypeT::Bool | TypeT::Int { .. }) => Some(a0),
            (TypeT::Bool | TypeT::Int { .. }, TypeT::PtrdiffT) => Some(b0),

            (TypeT::SizeT, TypeT::PtrdiffT) => Some(b0),
            (TypeT::PtrdiffT, TypeT::SizeT) => Some(a0),

            (TypeT::Int { .. }, TypeT::Bool) => Some(a0),
            (TypeT::Bool, TypeT::Int { .. }) => Some(b0),

            (TypeT::Float { width: w1 }, TypeT::Float { width: w2 }) => {
                if w1 >= w2 {
                    Some(a0)
                } else {
                    Some(b0)
                }
            }
            (
                TypeT::Float { .. },
                TypeT::Bool | TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT,
            ) => Some(a0),
            (
                TypeT::Bool | TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT,
                TypeT::Float { .. },
            ) => Some(b0),

            (
                TypeT::SLProp,
                TypeT::Bool
                | TypeT::Int { .. }
                | TypeT::SizeT
                | TypeT::PtrdiffT
                | TypeT::SpecInt
                | TypeT::SpecNat,
            ) => Some(a0),
            (
                TypeT::Bool
                | TypeT::Int { .. }
                | TypeT::SizeT
                | TypeT::PtrdiffT
                | TypeT::SpecInt
                | TypeT::SpecNat,
                TypeT::SLProp,
            ) => Some(b0),

            both_sides!(TypeT::Bool) => None,
            // Different Int types: use C-style usual arithmetic conversion
            (
                TypeT::Int {
                    signed: s1,
                    width: w1,
                },
                TypeT::Int {
                    signed: s2,
                    width: w2,
                },
            ) => {
                // Pick the wider type; if same width, pick unsigned
                let (signed, width) = if w1 > w2 {
                    (*s1, *w1)
                } else if w2 > w1 {
                    (*s2, *w2)
                } else {
                    // Same width: unsigned wins per C rules
                    (*s1 && *s2, *w1)
                };
                Some(TypeT::Int { signed, width }.with_loc(a.loc.clone()).into())
            }
            both_sides!(TypeT::SLProp) => None,
            both_sides!(TypeT::SizeT) => None,
            both_sides!(TypeT::PtrdiffT) => Some(a0),
            both_sides!(TypeT::SpecInt) => None,
            both_sides!(TypeT::SpecNat) => None,
            // SpecNat <: SpecInt
            (TypeT::SpecInt, TypeT::SpecNat) | (TypeT::SpecNat, TypeT::SpecInt) => None,

            either_side!(TypeT::Void) => None,
            either_side!(TypeT::Float { .. }) => None,
            either_side!(TypeT::Pointer(_, _)) => None,
            either_side!(TypeT::FixedArray(_, _)) => None,

            either_side!(TypeT::TypeRef(_)) => None,

            either_side!(
                TypeT::Refine(..)
                    | TypeT::RefineAlways(..)
                    | TypeT::RefineUninit(..)
                    | TypeT::RefineValue(..)
                    | TypeT::Plain(..)
                    | TypeT::Nullable(..)
            ) => None,
        }
    }

    pub fn vtype_whnf(&self, a: MaybeRc<Type>) -> MaybeRc<Type> {
        let mut a = a;
        while let Some(a_next) = self.vtype_whnf_step(&*a) {
            a = a_next
        }
        a
    }

    pub fn vtype_whnf_step(&self, a: &Type) -> Option<MaybeRc<Type>> {
        match &a.val {
            TypeT::Void
            | TypeT::Bool
            | TypeT::Int { .. }
            | TypeT::Float { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::Pointer(_, _)
            | TypeT::FixedArray(_, _)
            | TypeT::SpecInt
            | TypeT::SpecNat
            | TypeT::SLProp
            | TypeT::Unknown
            | TypeT::Error => None,

            TypeT::TypeRef(TypeRefKind::Typedef(n)) => {
                self.lookup_type(n).map(|defn| defn.body.clone().into())
            }
            TypeT::TypeRef(TypeRefKind::Struct(_)) => None,
            TypeT::TypeRef(TypeRefKind::Union(_)) => None,

            TypeT::Refine(ty, _)
            | TypeT::RefineAlways(ty, _)
            | TypeT::RefineUninit(ty, _)
            | TypeT::RefineValue(ty, ..)
            | TypeT::Plain(ty)
            | TypeT::Nullable(ty) => Some(ty.clone().into()),
        }
    }

    pub fn vtype_eq(&self, a: MaybeRc<Type>, b: MaybeRc<Type>) -> bool {
        match (&self.vtype_whnf(a).val, &self.vtype_whnf(b).val) {
            (TypeT::Void, TypeT::Void) => true,
            (TypeT::Bool, TypeT::Bool) => true,
            (
                TypeT::Int {
                    signed: s1,
                    width: w1,
                },
                TypeT::Int {
                    signed: s2,
                    width: w2,
                },
            ) => s1 == s2 && w1 == w2,
            (TypeT::Float { width: w1 }, TypeT::Float { width: w2 }) => w1 == w2,
            (TypeT::SizeT, TypeT::SizeT) => true,
            (TypeT::PtrdiffT, TypeT::PtrdiffT) => true,
            (TypeT::Pointer(t1, k1), TypeT::Pointer(t2, k2)) => {
                k1 == k2 && self.vtype_eq(t1.clone().into(), t2.clone().into())
            }
            (TypeT::FixedArray(t1, n1), TypeT::FixedArray(t2, n2)) => {
                n1 == n2 && self.vtype_eq(t1.clone().into(), t2.clone().into())
            }
            (TypeT::SpecInt, TypeT::SpecInt) => true,
            (TypeT::SpecNat, TypeT::SpecNat) => true,
            (TypeT::SLProp, TypeT::SLProp) => true,
            (TypeT::TypeRef(t1), TypeT::TypeRef(t2)) => t1.alpha_eq(t2),
            (TypeT::Error | TypeT::Unknown, _) | (_, TypeT::Error | TypeT::Unknown) => true,
            _ => false,
        }
    }

    pub fn is_bool(&self, a: MaybeRc<Type>) -> bool {
        matches!(&self.vtype_whnf(a).val, TypeT::Bool)
    }
    pub fn is_slprop(&self, a: MaybeRc<Type>) -> bool {
        matches!(&self.vtype_whnf(a).val, TypeT::SLProp)
    }

    pub fn is_lvalue(&self, expr: &Expr) -> bool {
        match &expr.val {
            ExprT::Var(x) => match self.lookup_var(x) {
                Some(decl) => decl.kind == LocalDeclKind::LValue,
                None => false,
            },
            ExprT::Deref(_) => true,
            ExprT::Member(x, _) => self.is_lvalue(x),
            ExprT::Index(_, _) => true,
            ExprT::Error(_) => true,
            _ => false,
        }
    }
}

impl_display_using_prettyir!(Env);

impl PrettyIR for Env {
    fn to_doc(&self) -> ::pretty::RcDoc<'_, ()> {
        use ::pretty::*;
        RcDoc::intersperse(
            self.locals.iter().map(|(local, LocalDecl { ty, kind })| {
                local
                    .to_doc()
                    .append(RcDoc::space())
                    .append(":")
                    .append(RcDoc::line())
                    .append(ty.to_doc())
                    .group()
                    .append(
                        RcDoc::line()
                            .append(match kind {
                                LocalDeclKind::LValue => "(lvalue)",
                                LocalDeclKind::RValue => "(rvalue)",
                            })
                            .group(),
                    )
                    .nest(2)
                    .group()
            }),
            RcDoc::hardline(),
        )
        .group()
    }
}
