//! Normalize out-of-range casts of integer literals before emission.
//!
//! C defines conversion to unsigned integers modulo 2^N. Conversion to a
//! signed type is implementation-defined when the value is not representable;
//! PAL consistently models it using the target-width two's-complement value.

use std::rc::Rc;

use num_bigint::BigInt;

use crate::{env::Env, ir::*};

/// Recover the mathematical unsigned value of an N-bit clang integer literal.
///
/// `toBigInt` in `cpp/impl.cpp` uses clang's signed rendering, so a high-bit
/// unsigned value can enter the IR as a negative `BigInt`.
pub(super) fn normalize_unsigned(value: &BigInt, width: u32) -> BigInt {
    let modulus = BigInt::from(1u32) << width;
    ((value % &modulus) + &modulus) % &modulus
}

fn normalize_signed(value: &BigInt, width: u32) -> BigInt {
    let modulus = BigInt::from(1u32) << width;
    let sign_bit = BigInt::from(1u32) << (width - 1);
    let unsigned = normalize_unsigned(value, width);
    if unsigned >= sign_bit {
        unsigned - modulus
    } else {
        unsigned
    }
}

fn integer_fits(value: &BigInt, signed: bool, width: u32) -> bool {
    if signed {
        let upper_exclusive = BigInt::from(1u32) << (width - 1);
        let lower_inclusive = -upper_exclusive.clone();
        value >= &lower_inclusive && value < &upper_exclusive
    } else {
        value >= &BigInt::ZERO && value < &(BigInt::from(1u32) << width)
    }
}

fn normalize_type(env: &Env, ty: &mut Rc<Type>) {
    match &mut Rc::make_mut(ty).val {
        TypeT::Pointer(inner, _)
        | TypeT::FixedArray(inner, _)
        | TypeT::FlexArray(inner)
        | TypeT::Plain(inner)
        | TypeT::Nullable(inner) => normalize_type(env, inner),
        TypeT::FnPtr { args, ret } => {
            for arg in args {
                normalize_type(env, arg);
            }
            normalize_type(env, ret);
        }
        TypeT::Refine(inner, pred)
        | TypeT::RefineAlways(inner, pred)
        | TypeT::RefineUninit(inner, pred) => {
            normalize_type(env, inner);
            normalize_expr(env, Rc::make_mut(pred));
        }
        TypeT::RefineValue(inner, _, binding_ty, pred) => {
            normalize_type(env, inner);
            normalize_type(env, binding_ty);
            normalize_expr(env, Rc::make_mut(pred));
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

fn normalize_inline_pulse(env: &Env, code: &mut InlinePulseCode) {
    for token in &mut code.tokens {
        match token {
            InlinePulseToken::RValueAntiquot { expr, .. }
            | InlinePulseToken::LValueAntiquot { expr, .. } => {
                normalize_expr(env, Rc::make_mut(expr));
            }
            InlinePulseToken::TypeAntiquot { ty, .. }
            | InlinePulseToken::FieldAntiquot { ty, .. }
            | InlinePulseToken::AuxFnAntiquot { ty, .. }
            | InlinePulseToken::Declare { ty, .. } => normalize_type(env, ty),
            InlinePulseToken::Verbatim(_) => {}
        }
    }
}

fn normalize_exprs(env: &Env, exprs: &mut Exprs) {
    for expr in exprs {
        normalize_expr(env, Rc::make_mut(expr));
    }
}

fn normalize_expr(env: &Env, expr: &mut Expr) {
    match &mut expr.val {
        ExprT::IntLit(_, ty)
        | ExprT::FloatLit(_, ty)
        | ExprT::Malloc(ty)
        | ExprT::Calloc(ty)
        | ExprT::SizeOf(ty)
        | ExprT::AlignOf(ty)
        | ExprT::Error(ty) => normalize_type(env, ty),
        ExprT::InlinePulse(code, ty) => {
            normalize_inline_pulse(env, Rc::make_mut(code));
            normalize_type(env, ty);
        }
        ExprT::Cast(value, ty)
        | ExprT::MallocArray(ty, value)
        | ExprT::CallocArray(ty, value)
        | ExprT::MallocFlex(ty, value)
        | ExprT::CallocFlex(ty, value)
        | ExprT::MemsetZero(ty, value) => {
            normalize_expr(env, Rc::make_mut(value));
            normalize_type(env, ty);
        }
        ExprT::ContainerOf(value, ty, _) => {
            normalize_expr(env, Rc::make_mut(value));
            normalize_type(env, ty);
        }
        ExprT::Forall(_, ty, body) | ExprT::Exists(_, ty, body) => {
            normalize_type(env, ty);
            normalize_expr(env, Rc::make_mut(body));
        }
        ExprT::ArrayInit { elem_ty, elems, .. } => {
            normalize_type(env, elem_ty);
            normalize_exprs(env, elems);
        }
        ExprT::Memset(ty, dest, value, count) => {
            normalize_type(env, ty);
            normalize_expr(env, Rc::make_mut(dest));
            normalize_expr(env, Rc::make_mut(value));
            normalize_expr(env, Rc::make_mut(count));
        }
        ExprT::Deref(value)
        | ExprT::Member(value, _)
        | ExprT::VAttr(_, value)
        | ExprT::Ref(value)
        | ExprT::UnOp(_, value)
        | ExprT::Live(value)
        | ExprT::Old(value)
        | ExprT::Free(value)
        | ExprT::PreIncr(value)
        | ExprT::PostIncr(value)
        | ExprT::PreDecr(value)
        | ExprT::PostDecr(value)
        | ExprT::UnionInit(_, _, value) => normalize_expr(env, Rc::make_mut(value)),
        ExprT::Index(left, right)
        | ExprT::BinOp(_, left, right)
        | ExprT::AssignExpr(left, right) => {
            normalize_expr(env, Rc::make_mut(left));
            normalize_expr(env, Rc::make_mut(right));
        }
        ExprT::Cond(cond, then_expr, else_expr) => {
            normalize_expr(env, Rc::make_mut(cond));
            normalize_expr(env, Rc::make_mut(then_expr));
            normalize_expr(env, Rc::make_mut(else_expr));
        }
        ExprT::FnCall(_, args) => normalize_exprs(env, args),
        ExprT::FnPtrCall(function, args) => {
            normalize_expr(env, Rc::make_mut(function));
            normalize_exprs(env, args);
        }
        ExprT::StructInit(_, fields) => {
            for (_, value) in fields {
                normalize_expr(env, Rc::make_mut(value));
            }
        }
        ExprT::Var(_) | ExprT::FnRef(_) | ExprT::BoolLit(_) => {}
    }

    let replacement = match &expr.val {
        ExprT::Cast(value, target_ty) => {
            let ExprT::IntLit(value, source_ty) = &value.val else {
                return;
            };
            let TypeT::Int {
                signed: target_signed,
                width: target_width,
            } = env.vtype_whnf(target_ty.clone().into()).val
            else {
                return;
            };
            let source_value = match env.vtype_whnf(source_ty.clone().into()).val {
                TypeT::Int {
                    signed: false,
                    width,
                } => normalize_unsigned(value, width),
                TypeT::Int { signed: true, .. } => value.as_ref().clone(),
                _ => return,
            };
            // Fold the cast away even when the value is representable. The
            // result is the same constant at the target type, and dropping the
            // conversion matters for more than readability: `Int.Cast` applied
            // to a literal reduces to a machine-integer constructor whose
            // argument carries a refinement only the SMT solver discharges, so
            // such a term is ill-typed wherever the checker runs without SMT --
            // notably while Pulse searches for a witness to an existential.
            let target_value = if integer_fits(&source_value, target_signed, target_width) {
                source_value
            } else if target_signed {
                normalize_signed(&source_value, target_width)
            } else {
                normalize_unsigned(&source_value, target_width)
            };
            Some(ExprT::IntLit(Rc::new(target_value), target_ty.clone()))
        }
        _ => None,
    };
    if let Some(replacement) = replacement {
        expr.val = replacement;
    }
}

fn normalize_stmt(env: &Env, stmt: &mut Stmt) {
    match &mut stmt.val {
        StmtT::Call(expr) | StmtT::Assert(expr) | StmtT::Return(Some(expr)) => {
            normalize_expr(env, Rc::make_mut(expr));
        }
        StmtT::Decl(_, ty) => normalize_type(env, ty),
        StmtT::Let(_, ty, value) => {
            normalize_type(env, ty);
            normalize_expr(env, Rc::make_mut(value));
        }
        StmtT::DeclStackArray {
            elem_type, size, ..
        } => {
            normalize_type(env, elem_type);
            normalize_expr(env, Rc::make_mut(size));
        }
        StmtT::Assign(left, right) => {
            normalize_expr(env, Rc::make_mut(left));
            normalize_expr(env, Rc::make_mut(right));
        }
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ensures,
        } => {
            normalize_expr(env, Rc::make_mut(cond));
            normalize_stmts(env, Rc::make_mut(then_branch));
            normalize_stmts(env, Rc::make_mut(else_branch));
            normalize_exprs(env, Rc::make_mut(ensures));
        }
        StmtT::Match {
            scrutinee,
            branches,
            default_branch,
            ensures,
        } => {
            normalize_expr(env, Rc::make_mut(scrutinee));
            for branch in Rc::make_mut(branches) {
                let branch = Rc::make_mut(branch);
                normalize_exprs(env, Rc::make_mut(&mut branch.patterns));
                normalize_stmts(env, Rc::make_mut(&mut branch.body));
            }
            normalize_stmts(env, Rc::make_mut(default_branch));
            normalize_exprs(env, Rc::make_mut(ensures));
        }
        StmtT::While {
            cond,
            inv,
            requires,
            ensures,
            body,
        } => {
            normalize_expr(env, Rc::make_mut(cond));
            normalize_exprs(env, Rc::make_mut(inv));
            normalize_exprs(env, Rc::make_mut(requires));
            normalize_exprs(env, Rc::make_mut(ensures));
            normalize_stmts(env, Rc::make_mut(body));
        }
        StmtT::GhostStmt(code) => normalize_inline_pulse(env, Rc::make_mut(code)),
        StmtT::Label { ensures, .. } => normalize_exprs(env, Rc::make_mut(ensures)),
        StmtT::GotoBlock { body, ensures, .. } => {
            normalize_stmts(env, Rc::make_mut(body));
            normalize_exprs(env, Rc::make_mut(ensures));
        }
        StmtT::Break | StmtT::Continue | StmtT::Return(None) | StmtT::Goto(_) | StmtT::Error => {}
    }
}

fn normalize_stmts(env: &Env, stmts: &mut Stmts) {
    for stmt in stmts {
        normalize_stmt(env, Rc::make_mut(stmt));
    }
}

fn normalize_fn_decl(env: &Env, decl: &mut FnDecl) {
    normalize_type(env, &mut decl.ret_type);
    for arg in &mut decl.args {
        normalize_type(env, &mut arg.ty);
    }
    for arg in &mut decl.ghost_args {
        normalize_type(env, &mut arg.ty);
    }
    normalize_exprs(env, &mut decl.requires);
    normalize_exprs(env, &mut decl.ensures);
    if let Some(decreases) = &mut decl.decreases {
        normalize_expr(env, Rc::make_mut(decreases));
    }
}

fn normalize_decl(env: &Env, decl: &mut Decl) {
    match &mut decl.val {
        DeclT::FnDefn(definition) => {
            normalize_fn_decl(env, &mut definition.decl);
            normalize_stmts(env, &mut definition.body);
        }
        DeclT::FnDecl(decl) => normalize_fn_decl(env, decl),
        DeclT::Typedef(definition) => normalize_type(env, &mut definition.body),
        DeclT::StructDefn(definition) => {
            for field in &mut definition.fields {
                match &mut field.val {
                    FieldT::Plain { ty, .. } | FieldT::BitField { ty, .. } => {
                        normalize_type(env, ty);
                    }
                }
            }
        }
        DeclT::UnionDefn(definition) => {
            for field in &mut definition.fields {
                match &mut field.val {
                    FieldT::Plain { ty, .. } | FieldT::BitField { ty, .. } => {
                        normalize_type(env, ty);
                    }
                }
            }
        }
        DeclT::IncludeDecl(include) => normalize_inline_pulse(env, &mut include.code),
        DeclT::LetDecl(decl) => {
            normalize_type(env, &mut decl.ret_type);
            for param in &mut decl.params {
                normalize_type(env, &mut param.ty);
            }
            normalize_exprs(env, &mut decl.requires);
            normalize_exprs(env, &mut decl.ensures);
            normalize_expr(env, Rc::make_mut(&mut decl.body));
        }
        DeclT::OpaqueTypeDecl(decl) => normalize_inline_pulse(env, &mut decl.code),
        DeclT::GlobalVar(global) => {
            normalize_type(env, &mut global.ty);
            if let Some(init) = &mut global.init {
                normalize_expr(env, Rc::make_mut(init));
            }
        }
        DeclT::StructDecl(_) => {}
    }
}

pub fn normalize_casts(tu: &mut TranslationUnit) {
    let mut env = Env::new();
    for decl in &tu.decls {
        env.push_decl(decl);
    }
    for decl in &mut tu.decls {
        normalize_decl(&env, decl);
    }
}
