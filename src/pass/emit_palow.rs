//! Palow-mode emission: milestone 2, stage 1.
//!
//! Behind `--palow`, this emits the *specification surface* of a translation
//! unit against the Palow memory model (`pulse/Pulse.Lib.C.Palow.*`) instead of
//! `Pulse.Lib.Reference`. It is deliberately a separate emitter rather than a
//! branch inside [`crate::pass::emit`]: the two models disagree about the F*
//! type of a pointer, which is the top of the dependency chain for everything
//! that emitter does, so interleaving them would mean threading a mode flag
//! through several thousand lines. Keeping them apart lets the existing test
//! suite stay green while the port proceeds.
//!
//! What is emitted is a Pulse *interface* -- `fn` declarations with no bodies,
//! which F* typechecks exactly as it does `Pulse.Lib.C.Palow.Machine.fsti`.
//! That is enough to check the part of the port that carries all the model
//! choices: how a C type becomes an F* type, and how a pointer parameter
//! becomes ownership. Bodies, and translating the user's `_requires`/`_ensures`
//! predicates, are the next stage; functions get a comment saying so rather
//! than silently pretending their contracts were translated.
//!
//! The comparison worth making is with today's output for `test/swap/swap.c`:
//!
//! ```text
//!   fn func_swap (var_x: (ref Int32.t)) (var_y: (ref Int32.t))
//!     requires exists* (val_x_0: Int32.t). Pulse.Lib.Reference.pts_to var_x #1.0R val_x_0
//! ```
//!
//! versus
//!
//! ```text
//!   fn func_swap (var_x: ptr) (var_y: ptr) (#val_x: erased Int32.t) ...
//!     requires int32_t_pts_to var_x 1.0R val_x
//! ```
//!
//! The parameter's F* type no longer depends on how the pointer is used, which
//! is the property that makes the pointer-kind inference in
//! [`crate::pass::elab`] unnecessary.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ir::*;

/// C code names its scalars through typedefs (`uint32_t`, `my_len_t`, ...), so
/// without unfolding them almost nothing in the test suite would be
/// translatable. Struct and union typedefs are left folded; they are milestone
/// 4's problem, and unfolding them here would only change the wording of the
/// skip message.
struct Typedefs<'a>(HashMap<&'a str, &'a Rc<Type>>);

impl<'a> Typedefs<'a> {
    fn new(tu: &'a TranslationUnit) -> Self {
        let mut m = HashMap::new();
        for decl in &tu.decls {
            if let DeclT::Typedef(td) = &decl.val {
                m.insert(&*td.name.val, &td.body);
            }
        }
        Typedefs(m)
    }

    fn resolve<'b>(&'b self, ty: &'b Type) -> &'b Type
    where
        'a: 'b,
    {
        let mut ty = ty;
        // Typedefs cannot be cyclic in valid C, but bound the walk anyway
        // rather than trust the input.
        for _ in 0..64 {
            match &ty.val {
                TypeT::TypeRef(TypeRefKind::Typedef(n)) => match self.0.get(&*n.val) {
                    Some(body) => ty = body,
                    None => return ty,
                },
                _ => return ty,
            }
        }
        ty
    }
}

/// How a type is described in a skip message.
fn describe(ty: &Type) -> String {
    match &ty.val {
        TypeT::Void => "void".to_string(),
        TypeT::Bool => "_Bool".to_string(),
        TypeT::Int { signed, width } => {
            format!("{}int{}_t", if *signed { "" } else { "u" }, width)
        }
        TypeT::Pointer(..) => "a pointer".to_string(),
        TypeT::SpecInt | TypeT::SpecNat | TypeT::SLProp => "a specification type".to_string(),
        TypeT::Unknown | TypeT::Error => "an unresolved type".to_string(),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => describe(t),
        TypeT::Float { width } => format!("a {}-bit float", width),
        TypeT::SizeT => "size_t".to_string(),
        TypeT::PtrdiffT => "ptrdiff_t".to_string(),
        TypeT::FnPtr { .. } => "a function pointer".to_string(),
        TypeT::FixedArray(..) | TypeT::FlexArray(..) => "an array".to_string(),
        TypeT::TypeRef(TypeRefKind::Struct(n)) => format!("struct {}", n.val),
        TypeT::TypeRef(TypeRefKind::Union(n)) => format!("union {}", n.val),
        TypeT::TypeRef(TypeRefKind::Typedef(n)) => format!("typedef {}", n.val),
        _ => "an unsupported type".to_string(),
    }
}

pub struct PalowModule {
    pub module_name: String,
    pub code: String,
}

/// The Palow name of a C type: the prefix of its `_pts_to`, `_repr`, `_read`
/// and `_sizeof` definitions. `None` for types the model does not cover yet.
fn palow_name(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &tds.resolve(ty).val {
        TypeT::Bool => Some("bool_t".to_string()),
        TypeT::Int { signed, width } => {
            Some(format!("{}int{}_t", if *signed { "" } else { "u" }, width))
        }
        TypeT::SizeT => Some("size_t".to_string()),
        // Every pointer kind is the same type here; that is the point.
        TypeT::Pointer(..) => Some("ptr".to_string()),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => palow_name(tds, t),
        _ => None,
    }
}

/// The F* type of a C value.
fn fstar_type(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &tds.resolve(ty).val {
        TypeT::Void => Some("unit".to_string()),
        TypeT::Bool => Some("bool".to_string()),
        TypeT::Int { signed, width } => {
            Some(format!("{}Int{}.t", if *signed { "" } else { "U" }, width))
        }
        TypeT::SizeT => Some("SizeT.t".to_string()),
        TypeT::Pointer(..) => Some("ptr".to_string()),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => fstar_type(tds, t),
        _ => None,
    }
}

/// How much memory a pointer parameter owns. Palow makes every C pointer the
/// same F* *type*, which is what removes the pointer-kind inference from
/// `elab` -- but it does not make the *extent* of the ownership go away. A
/// `T *` that C uses as an array still has to appear in the contract as an
/// array, and clang's pointer kind is what tells us which it is. The
/// distinction moves from the type to the specification; it does not vanish.
#[derive(Clone, Copy, PartialEq)]
enum Extent {
    One,
    Array,
}

fn extent(tds: &Typedefs, ty: &Type) -> Option<Extent> {
    match &tds.resolve(ty).val {
        TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr) => Some(Extent::Array),
        TypeT::Pointer(..) => Some(Extent::One),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => extent(tds, t),
        _ => None,
    }
}

/// The size in bytes of a type the model covers. These are clang's LP64 sizes,
/// which the rest of the model already assumes.
fn palow_sizeof(tds: &Typedefs, ty: &Type) -> Option<u64> {
    match &tds.resolve(ty).val {
        TypeT::Bool => Some(1),
        TypeT::Int { width, .. } => Some((*width / 8) as u64),
        TypeT::SizeT | TypeT::PtrdiffT | TypeT::Pointer(..) | TypeT::FnPtr { .. } => Some(8),
        TypeT::FixedArray(t, n) => palow_sizeof(tds, t).map(|s| s * n),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => palow_sizeof(tds, t),
        _ => None,
    }
}

/// The alignment of a type the model covers. Every scalar Palow knows about is
/// aligned to its own width on LP64, and an array is aligned like its element.
fn palow_alignof(tds: &Typedefs, ty: &Type) -> Option<u64> {
    match &tds.resolve(ty).val {
        TypeT::FixedArray(t, _) => palow_alignof(tds, t),
        _ => palow_sizeof(tds, ty),
    }
}

/// Whether a parameter type carries a `_refine`, anywhere under the wrappers
/// or through the pointer.
fn refined(tds: &Typedefs, ty: &Type) -> bool {
    match &tds.resolve(ty).val {
        TypeT::Refine(..) | TypeT::RefineAlways(..) | TypeT::RefineUninit(..) => true,
        TypeT::RefineValue(t, ..) | TypeT::Plain(t) | TypeT::Nullable(t) | TypeT::Pointer(t, _) => {
            refined(tds, t)
        }
        _ => false,
    }
}

/// The pointee of a pointer parameter, skipping the wrappers that do not
/// change the representation.
fn pointee<'a>(tds: &'a Typedefs, ty: &'a Type) -> Option<&'a Rc<Type>> {
    match &tds.resolve(ty).val {
        TypeT::Pointer(to, _) => Some(to),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => pointee(tds, t),
        _ => None,
    }
}

/// A `const` pointer parameter is read-only, so it needs a fraction rather than
/// full ownership. Under Palow this is the *only* thing that distinguishes it:
/// the type is `ptr` either way.
fn is_shared(mode: ParamMode) -> bool {
    matches!(mode, ParamMode::Const)
}

struct FnSurface {
    decl: String,
    /// Whether the C function's own `_requires`/`_ensures` made it into the
    /// specification. When they did not, the contract we emit is weaker than
    /// the source says, and in particular cannot discharge an overflow
    /// obligation -- see `Body::signed_ok`.
    contract: bool,
}

/// Which values a specification expression refers to: the ones on entry, the
/// ones on exit, or -- inside `_old` -- the ones on entry again.
#[derive(Clone, Copy, PartialEq)]
enum When {
    Pre,
    Post,
    Old,
}

/// Enough of the function's signature to translate its contract: what each
/// pointer parameter's pointee is called before and after the call, and what
/// the result is called.
struct Spec<'a> {
    tds: &'a Typedefs<'a>,
    env: &'a Env,
    /// C parameter name -> (term for the pointee on entry, on exit).
    /// `None` on entry means an `_out` parameter, which has no incoming value;
    /// `None` on exit means ownership the function does not give back.
    pointees: HashMap<String, (Option<String>, Option<String>)>,
    /// Parameters whose `pointees` entry is a sequence rather than a value.
    arrays: HashSet<String>,
    /// Well-definedness side conditions raised while translating the clause
    /// currently in flight. `Seq.index` is partial, and a postcondition cannot
    /// appeal to the precondition for its own typing, so the bound has to be
    /// conjoined into the same proposition.
    guards: RefCell<Vec<String>>,
    ret: String,
}

impl<'a> Spec<'a> {
    fn int_module(&self, ty: &Type) -> Option<String> {
        match &self.tds.resolve(ty).val {
            TypeT::Int { signed, width } => {
                Some(format!("{}Int{}", if *signed { "" } else { "U" }, width))
            }
            TypeT::SizeT => Some("SizeT".to_string()),
            _ => None,
        }
    }

    fn ty_of(&self, e: &Expr) -> Result<Rc<Type>, String> {
        self.env
            .infer_expr(e)
            .map(|t| t.to_rc())
            .map_err(|_| "a subexpression whose type could not be inferred".to_string())
    }

    /// A specification expression in proposition position.
    fn prop(&self, e: &Expr, w: When) -> Result<String, String> {
        match &e.val {
            ExprT::Cast(inner, to) if matches!(self.tds.resolve(to).val, TypeT::SLProp) => {
                self.prop(inner, w)
            }
            ExprT::Old(inner) => self.prop(inner, When::Old),
            ExprT::UnOp(UnOp::Not, inner) => Ok(format!("(~({}))", self.prop(inner, w)?)),
            ExprT::BoolLit(b) => Ok(if *b { "True" } else { "False" }.to_string()),
            ExprT::BinOp(op, l, r) => {
                let logical = match op {
                    BinOp::LogAnd => Some("/\\"),
                    BinOp::LogOr => Some("\\/"),
                    BinOp::Implies => Some("==>"),
                    _ => None,
                };
                if let Some(o) = logical {
                    return Ok(format!("({} {} {})", self.prop(l, w)?, o, self.prop(r, w)?));
                }
                let ty = self.ty_of(l)?;
                if matches!(op, BinOp::Eq) {
                    // `_Bool` equality is equivalence of the two conditions,
                    // not equality of two values: one side is often a
                    // comparison, which has no value in F*.
                    if matches!(self.tds.resolve(&ty).val, TypeT::Bool) {
                        return Ok(format!("({} <==> {})", self.prop(l, w)?, self.prop(r, w)?));
                    }
                    // `num` rather than `value`: machine-integer `v` is
                    // injective, so this is the same proposition, and it is
                    // the only form that also works for `p._length`.
                    return Ok(format!("({} == {})", self.num(l, w)?, self.num(r, w)?));
                }
                let o = match op {
                    BinOp::Lt => "<",
                    BinOp::LEq => "<=",
                    _ => return Err("an unsupported operator in a contract".to_string()),
                };
                // C compares machine integers directly; F* orders only
                // mathematical ones, so an uncast comparison needs the `.v`
                // that an explicit `(_specint)` would have supplied.
                Ok(format!("({} {} {})", self.num(l, w)?, o, self.num(r, w)?))
            }
            _ => {
                // A bare `_Bool`-valued condition.
                let ty = self.ty_of(e)?;
                if matches!(self.tds.resolve(&ty).val, TypeT::Bool) {
                    Ok(format!("({} == true)", self.value(e, w)?))
                } else {
                    Err(format!("{} in a contract", expr_kind(e)))
                }
            }
        }
    }

    /// A specification expression as a mathematical integer.
    /// `p._length` is the one specification form that is already
    /// mathematical: an array parameter's ownership *is* a sequence, so the
    /// length is `Seq.length` of it and never goes through `SizeT.v`.
    fn length_of(&self, e: &Expr, w: When) -> Option<Result<String, String>> {
        let ExprT::VAttr(VAttr::Length, inner) = &e.val else {
            return None;
        };
        let ExprT::Var(v) = &inner.val else {
            return Some(Err("`_length` of a computed pointer".to_string()));
        };
        Some(match self.pointees.get(&*v.val) {
            None => Err(format!("`{}._length` in a contract", v.val)),
            Some((pre, post)) => {
                let chosen = match w {
                    When::Post => post,
                    When::Pre | When::Old => pre,
                };
                match chosen {
                    Some(s) => Ok(format!("(Seq.length {})", s)),
                    None => Err(format!("`{}._length` is not available here", v.val)),
                }
            }
        })
    }

    /// `*p` and `p[i]`. For a scalar parameter the pointee *is* the ghost
    /// value; for an array parameter it is an index into the ghost sequence,
    /// which is why the two cannot share a translation.
    fn pointee_at(&self, base: &Expr, idx: Option<&Expr>, w: When) -> Result<String, String> {
        let ExprT::Var(v) = &base.val else {
            return Err("a contract that dereferences a computed pointer".to_string());
        };
        let Some((pre, post)) = self.pointees.get(&*v.val) else {
            return Err(format!("`*{}` in a contract", v.val));
        };
        let chosen = match w {
            When::Post => post,
            When::Pre | When::Old => pre,
        };
        let Some(term) = chosen else {
            return Err(format!(
                "`*{}` has no {} value",
                v.val,
                if w == When::Post { "final" } else { "initial" }
            ));
        };
        if self.arrays.contains(&*v.val) {
            let i = match idx {
                None => "0".to_string(),
                Some(i) => self.num(i, w)?,
            };
            self.guards
                .borrow_mut()
                .push(format!("{} < Seq.length {}", i, term));
            Ok(format!("(Seq.index {} {})", term, i))
        } else if idx.is_some() {
            Err(format!("`{}[i]` on a non-array in a contract", v.val))
        } else {
            Ok(term.clone())
        }
    }

    fn num(&self, e: &Expr, w: When) -> Result<String, String> {
        if let ExprT::Old(inner) = &e.val {
            return self.num(inner, When::Old);
        }
        if let Some(l) = self.length_of(e, w) {
            return l;
        }
        let ty = self.ty_of(e)?;
        match self.int_module(&ty) {
            Some(m) => Ok(format!("({}.v {})", m, self.value(e, w)?)),
            None => self.value(e, w),
        }
    }

    /// A specification expression in value position.
    fn value(&self, e: &Expr, w: When) -> Result<String, String> {
        match &e.val {
            ExprT::Old(inner) => self.value(inner, When::Old),
            ExprT::Cast(inner, to) => {
                let to = self.tds.resolve(to);
                match &to.val {
                    // `(_specint) e` is where a machine value becomes a
                    // mathematical one. This is what lets a contract state an
                    // overflow bound at all, so it is the case that matters.
                    TypeT::SpecInt | TypeT::SpecNat => {
                        if let Some(l) = self.length_of(inner, w) {
                            return l;
                        }
                        let ity = self.ty_of(inner)?;
                        match self.int_module(&ity) {
                            Some(m) => Ok(format!("({}.v {})", m, self.value(inner, w)?)),
                            None if matches!(
                                self.tds.resolve(&ity).val,
                                TypeT::SpecInt | TypeT::SpecNat
                            ) =>
                            {
                                self.value(inner, w)
                            }
                            // C's integer promotion of `_Bool`.
                            None if matches!(self.tds.resolve(&ity).val, TypeT::Bool) => {
                                Ok(format!("(if {} then 1 else 0)", self.value(inner, w)?))
                            }
                            None => Err(format!(
                                "a contract that measures {}",
                                describe(self.tds.resolve(&ity))
                            )),
                        }
                    }
                    _ => {
                        let from = self.ty_of(inner)?;
                        if fstar_type(self.tds, &from) == fstar_type(self.tds, to) {
                            self.value(inner, w)
                        } else {
                            Err(format!(
                                "a contract converting {} to {}",
                                describe(self.tds.resolve(&from)),
                                describe(to)
                            ))
                        }
                    }
                }
            }
            ExprT::Var(v) => {
                if &*v.val == "return" {
                    Ok(self.ret.clone())
                } else if self.env.lookup_var(v).is_some() {
                    Ok(format!("var_{}", v.val))
                } else {
                    Err(format!("`{}` in a contract", v.val))
                }
            }
            ExprT::Deref(inner) => self.pointee_at(inner, None, w),
            ExprT::Index(base, idx) => self.pointee_at(base, Some(idx), w),
            ExprT::UnOp(op, inner) => {
                let ety = self.ty_of(e)?;
                let ty = self.tds.resolve(&ety);
                match (op, &ty.val) {
                    // Only at specification level, where there is no
                    // wraparound to get wrong.
                    (UnOp::Neg, TypeT::SpecInt | TypeT::SpecNat) => {
                        Ok(format!("(0 - {})", self.value(inner, w)?))
                    }
                    (UnOp::Not, TypeT::Bool) => Ok(format!("(not {})", self.value(inner, w)?)),
                    _ => Err(format!(
                        "`{}` on {} in a contract",
                        op.to_str(),
                        describe(ty)
                    )),
                }
            }
            ExprT::BoolLit(b) => Ok(if *b { "true" } else { "false" }.to_string()),
            ExprT::IntLit(n, ty) => match &self.tds.resolve(ty).val {
                TypeT::SpecInt | TypeT::SpecNat => Ok(if **n < BigInt::ZERO {
                    format!("({})", n)
                } else {
                    n.to_string()
                }),
                _ => int_literal(self.tds, n, ty),
            },
            ExprT::BinOp(op, l, r) => {
                let ty = self.ty_of(l)?;
                if !matches!(self.tds.resolve(&ty).val, TypeT::SpecInt | TypeT::SpecNat) {
                    return Err("arithmetic on machine integers in a contract".to_string());
                }
                let o = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::Mod => "%",
                    _ => return Err("an unsupported operator in a contract".to_string()),
                };
                Ok(format!(
                    "({} {} {})",
                    self.value(l, w)?,
                    o,
                    self.value(r, w)?
                ))
            }
            _ => Err(format!("{} in a contract", expr_kind(e))),
        }
    }
}

/// Build the Pulse declaration for one C function, or explain why we cannot.
fn emit_fn(tds: &Typedefs, env: &Env, decl: &FnDecl) -> Result<FnSurface, String> {
    let name = format!("func_{}", decl.name.val);

    let mut params: Vec<String> = Vec::new();
    let mut ghosts: Vec<String> = Vec::new();
    let mut perms: Vec<String> = Vec::new();
    let mut req: Vec<String> = Vec::new();
    let mut preserved: Vec<String> = Vec::new();
    // Ownership handed back with a value the contract may constrain: the
    // existential binder, its type, and the points-to less its value argument.
    let mut fresh: Vec<(String, String, String)> = Vec::new();
    let mut pointees: HashMap<String, (Option<String>, Option<String>)> = HashMap::new();
    let mut arrays: HashSet<String> = HashSet::new();

    for (i, arg) in decl.args.iter().enumerate() {
        let pname = match &arg.name {
            Some(n) => format!("var_{}", n.val),
            None => format!("arg_{}", i),
        };
        let fty = fstar_type(tds, &arg.ty)
            .ok_or_else(|| format!("parameter {} is {}", pname, describe(tds.resolve(&arg.ty))))?;
        params.push(format!("({}: {})", pname, fty));

        let Some(pt) = pointee(tds, &arg.ty) else {
            continue;
        };
        let pn = palow_name(tds, pt).ok_or_else(|| {
            format!(
                "parameter {} points to {}",
                pname,
                describe(tds.resolve(pt))
            )
        })?;
        let vty = fstar_type(tds, pt).unwrap();
        let base = pname.trim_start_matches("var_").to_string();
        let vname = format!("val_{}", base);

        // `T *p` owns one `T`; `T p[]` owns a sequence of them. Same F* type,
        // different contract.
        let (vty, pts_to): (String, Box<dyn Fn(&str, &str) -> String>) =
            match extent(tds, &arg.ty).unwrap() {
                Extent::One => {
                    let pn = pn.clone();
                    let p = pname.clone();
                    (
                        vty,
                        Box::new(move |perm: &str, v: &str| {
                            format!("{}_pts_to {} {} {}", pn, p, perm, v)
                        }),
                    )
                }
                Extent::Array => {
                    arrays.insert(base.clone());
                    let esize = palow_sizeof(tds, pt).ok_or_else(|| {
                        format!("parameter {} is an array of {}", pname, describe(pt))
                    })?;
                    let pn = pn.clone();
                    let p = pname.clone();
                    (
                        format!("Seq.seq {}", vty),
                        Box::new(move |perm: &str, v: &str| {
                            format!("array_pts_to {}_repr {} {} {} {}", pn, esize, p, perm, v)
                        }),
                    )
                }
            };

        match arg.mode {
            // `_out`: the callee is handed storage, not a value. This is the
            // one parameter mode the current model cannot express at all --
            // a `ref t` always holds a `t` -- and here it is just the
            // uninitialised points-to.
            ParamMode::Out if extent(tds, &arg.ty) == Some(Extent::One) => {
                req.push(format!("{}_pts_to_uninit {}", pn, pname));
                fresh.push((format!("{}'", vname), vty, pts_to("1.0R", "")));
                pointees.insert(base, (None, Some(format!("{}'", vname))));
            }
            ParamMode::Out => return Err(format!("parameter {} is an `_out` array", pname)),
            ParamMode::Const => {
                let perm = format!("perm_{}", base);
                perms.push(format!("(#{}: perm)", perm));
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                preserved.push(pts_to(&perm, &vname));
                let v = format!("(reveal {})", vname);
                pointees.insert(base, (Some(v.clone()), Some(v)));
            }
            ParamMode::Consumed => {
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                req.push(pts_to("1.0R", &vname));
                pointees.insert(base, (Some(format!("(reveal {})", vname)), None));
            }
            ParamMode::Regular => {
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                req.push(pts_to("1.0R", &vname));
                fresh.push((format!("{}'", vname), vty, pts_to("1.0R", "")));
                pointees.insert(
                    base,
                    (
                        Some(format!("(reveal {})", vname)),
                        Some(format!("{}'", vname)),
                    ),
                );
            }
        }
    }

    let ret = fstar_type(tds, &decl.ret_type)
        .ok_or_else(|| format!("it returns {}", describe(tds.resolve(&decl.ret_type))))?;
    let ret_name = format!("ret_{}", decl.name.val);

    // The contract is all-or-nothing: a half-translated one would be silently
    // weaker in a way nothing downstream could detect.
    let spec = Spec {
        tds,
        env,
        pointees,
        arrays,
        guards: RefCell::new(Vec::new()),
        ret: ret_name.clone(),
    };
    let translate = |es: &Exprs, w: When| -> Result<Vec<String>, String> {
        es.iter()
            .map(|e| {
                spec.guards.borrow_mut().clear();
                let p = spec.prop(e, w)?;
                let guards = spec.guards.borrow();
                Ok(if guards.is_empty() {
                    p
                } else {
                    format!("{} /\\ {}", guards.join(" /\\ "), p)
                })
            })
            .collect()
    };
    let contract = translate(&decl.requires, When::Pre)
        .and_then(|pre| translate(&decl.ensures, When::Post).map(|post| (pre, post)));
    let (pre_props, post_props, contract_ok, dropped) = match contract {
        Ok((pre, post)) => (pre, post, true, None),
        Err(why) => (
            Vec::new(),
            Vec::new(),
            decl.requires.is_empty() && decl.ensures.is_empty(),
            Some(why),
        ),
    };

    let mut out = String::new();
    if let Some(why) = dropped {
        // Silently weakening a contract would be undetectable downstream, so
        // say so in the generated file.
        out += &format!("(* contract dropped: {} *)\n", why);
    }
    out += &format!("fn {}", name);
    if params.is_empty() && perms.is_empty() && ghosts.is_empty() {
        // Pulse has no nullary `fn`; `f(void)` becomes `f ()`.
        out += " ()";
    }
    for p in params.iter().chain(perms.iter()).chain(ghosts.iter()) {
        out += &format!(" {}", p);
    }
    out += "\n";

    for slprop in &preserved {
        out += &format!("  preserves {}\n", slprop);
    }
    let mut req = req;
    req.extend(pre_props.iter().map(|p| format!("pure ({})", p)));
    if req.is_empty() {
        out += "  requires emp\n";
    } else {
        out += &format!("  requires {}\n", req.join(" **\n           "));
    }
    out += &format!("  returns  {} : {}\n", ret_name, ret);

    let mut bodies: Vec<String> = fresh
        .iter()
        .map(|(b, _, s)| format!("{} {}", s.trim_end(), b))
        .collect();
    bodies.extend(post_props.iter().map(|p| format!("pure ({})", p)));
    if bodies.is_empty() {
        out += "  ensures  emp\n";
    } else if fresh.is_empty() {
        out += &format!("  ensures  {}\n", bodies.join(" **\n           "));
    } else {
        let binders: Vec<String> = fresh
            .iter()
            .map(|(b, t, _)| format!("({}: {})", b, t))
            .collect();
        out += &format!(
            "  ensures  exists* {}.\n             {}\n",
            binders.join(" "),
            bodies.join(" **\n             ")
        );
    }

    Ok(FnSurface {
        decl: out,
        contract: contract_ok,
    })
}

const HEADER: &str = r#"(* Generated by pal --palow.

   This is the translation unit in the Palow memory model: the F* type of every
   parameter, the ownership its contract needs, and -- where the translation
   covers it -- the body. See milestone 2 in palow.md.

   Two things are not translated yet, and both make the specifications weaker
   than the ones PAL emits today rather than wrong. The user's own
   `_requires`/`_ensures` predicates are dropped, so a postcondition says only
   what memory comes back, not what is in it. And bodies outside the
   straight-line scalar subset are `admit()`ed; the count of those is the
   coverage measurement this file exists to produce. *)
"#;

pub fn emit_palow(tu: &TranslationUnit) -> Vec<PalowModule> {
    let tds = Typedefs::new(tu);
    let mut base = Env::new();
    for decl in &tu.decls {
        base.push_decl(decl);
    }
    let mut code = String::new();
    code += "module PalowSpecs\n";
    code += HEADER;
    code += "\n#lang-pulse\nopen Pulse\n";
    code += "open Pulse.Lib.C.Palow.Bytes\n";
    code += "open Pulse.Lib.C.Palow.Ptr\n";
    code += "open Pulse.Lib.C.Palow\n";
    code += "open Pulse.Lib.C.Palow.Scalar\n";
    code += "open Pulse.Lib.C.Palow.CTypes\n";
    code += "open Pulse.Lib.C.Palow.Machine\n";
    code += "open Pulse.Lib.C.Palow.Array\n";
    code += "module Seq = FStar.Seq\n\n";
    for m in ["Int8", "Int16", "Int32", "Int64"] {
        code += &format!("module {} = FStar.{}\n", m, m);
    }
    for m in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        code += &format!("module {} = FStar.{}\n", m, m);
    }
    code += "module SizeT = FStar.SizeT\n\n";

    let mut callees: HashMap<String, Callee> = HashMap::new();
    for decl in &tu.decls {
        let (fndecl, defn) = match &decl.val {
            DeclT::FnDefn(d) => (&d.decl, Some(d)),
            DeclT::FnDecl(d) => (d, None),
            _ => continue,
        };
        let mut env = base.clone();
        env.push_fn_decl_args_for_body(fndecl);
        let sig = match emit_fn(&tds, &env, fndecl) {
            Ok(s) => s,
            Err(why) => {
                code += &format!("(* skipped {}: {} *)\n\n", fndecl.name.val, why);
                continue;
            }
        };

        let body = match defn {
            None => Err("it has no definition here".to_string()),
            Some(d) => emit_body(&tds, env, d, &sig, &callees),
        };
        code += &sig.decl;
        match body {
            Ok(lines) => {
                code += "{\n";
                for l in &lines {
                    code += &format!("  {}\n", l);
                }
                code += "}\n\n";
            }
            Err(why) => {
                code += &format!("{{\n  admit() (* body: {} *)\n}}\n\n", why);
            }
        }

        // A call may only pass ownership it can name: a value, or a pointer to
        // an object the caller holds and gets back unchanged. `_out` and
        // `_consumes` parameters move ownership across the call, which the
        // caller's slot bookkeeping does not model yet.
        callees.insert(
            fndecl.name.val.to_string(),
            Callee {
                simple: fndecl
                    .args
                    .iter()
                    .all(|a| matches!(a.mode, ParamMode::Regular | ParamMode::Const))
                    && fndecl.ghost_args.is_empty()
                    && !fndecl
                        .args
                        .iter()
                        .any(|a| extent(&tds, &a.ty) == Some(Extent::Array))
                    // A `_refine` on a parameter is part of the contract on
                    // both sides of the call, and is not translated yet; a
                    // caller that could not see it would be proving against a
                    // specification weaker than the source's.
                    && !fndecl.args.iter().any(|a| refined(&tds, &a.ty)),
                void: matches!(tds.resolve(&fndecl.ret_type).val, TypeT::Void),
                contract: sig.contract,
            },
        );
    }

    vec![PalowModule {
        module_name: "PalowSpecs".to_string(),
        code,
    }]
}

/* ---------------------------------------------------------------------------
Bodies

Stage 2. The specification surface above says what a function's contract
looks like in the Palow model; this says what its code looks like. The
subset is deliberately narrow -- straight-line scalar code -- because the
constructs left out (`if`, `while`, calls) need things that are not yet
translated: a loop needs the user's `_invariant`, and a call needs the
callee's real contract rather than the weakest one we currently emit.
Everything outside the subset gets an `admit()`, so the module still
typechecks as a whole and the number of `admit()`s is a coverage number that
should fall as the port proceeds.

Every C local becomes a stack slot rather than an F* `let`. A slot is more
code than a `let` when the local is never assigned and never has its address
taken, but deciding that needs an analysis, and getting it wrong is silent:
an F* `let` cannot model an assignment. The optimisation is worth making
later, on measurements, not now.
--------------------------------------------------------------------------- */

use crate::env::Env;
use num_bigint::BigInt;

/// A C local's automatic storage. `init` tracks whether anything has been
/// stored yet, because an uninitialised slot takes `_write_uninit` rather than
/// `_write`, and releasing one must not `_forget` a value it never held.
/// Tracking this with a flag is only sound because the translated subset is
/// straight-line; a branch would need a join.
struct Slot {
    name: String,
    palow_ty: String,
    init: bool,
}

/// What one arm of an `if` produced: its statements, and the state it leaves
/// the enclosing scope in.
struct BranchResult {
    lines: Vec<String>,
    inits: Vec<bool>,
    out_params: Vec<String>,
}

fn indent(line: &str) -> String {
    format!("  {}", line)
}

/// What the emitter needs to know about a function it has already emitted in
/// order to call it: whether every parameter is one the call translation can
/// pass, and whether the result is a value.
struct Callee {
    simple: bool,
    void: bool,
    /// Whether the callee's own `_requires`/`_ensures` were translated. If they
    /// were not its specification says only what memory comes back, and a
    /// caller that has a contract of its own has nothing to prove it with.
    contract: bool,
}

struct Body<'a> {
    tds: &'a Typedefs<'a>,
    env: Env,
    /// Functions emitted earlier in this module, by C name. A call to anything
    /// else -- a function defined further down the file, or one whose
    /// specification was skipped -- has no name to refer to.
    callees: &'a HashMap<String, Callee>,
    lines: Vec<String>,
    /// C locals with a stack slot, in allocation order.
    slots: Vec<Slot>,
    /// Pointer parameters declared `_out`: they arrive holding storage rather
    /// than a value, so the first store through one is an initialising store.
    out_params: Vec<String>,
    tmp: usize,
    /// Whether signed arithmetic may be emitted. Its overflow obligation is
    /// discharged by the function's `_requires` clause, so emitting it without
    /// one produces a failure that says nothing about the memory model.
    signed_ok: bool,
    /// Whether this function has a contract to prove. If it does not, a call
    /// to a function whose own contract was dropped is harmless.
    has_contract: bool,
}

impl<'a> Body<'a> {
    fn fresh(&mut self, hint: &str) -> String {
        self.tmp += 1;
        format!("tmp{}_{}", self.tmp, hint)
    }

    fn ty_of(&self, e: &Expr) -> Result<Rc<Type>, String> {
        self.env
            .infer_expr(e)
            .map(|t| t.to_rc())
            .map_err(|_| "the type of a subexpression could not be inferred".to_string())
    }

    /// The address of an lvalue, as an F* expression of type `ptr`.
    fn addr(&mut self, e: &Expr) -> Result<String, String> {
        match &e.val {
            ExprT::Var(v) => {
                if self.slots.iter().any(|s| s.name == *v.val) {
                    Ok(format!("loc_{}", v.val))
                } else {
                    // A parameter of scalar type has no address in the Palow
                    // model unless the C code takes one, in which case the
                    // translation would have to give it a slot too.
                    Err(format!("`{}` has no address", v.val))
                }
            }
            ExprT::Deref(inner) => self.rvalue(inner),
            ExprT::VAttr(_, inner) => self.addr(inner),
            _ => Err("unsupported lvalue".to_string()),
        }
    }

    /// An rvalue, as an F* expression. Reads are effectful, so they are bound
    /// to a fresh name and the binding is pushed onto `lines`.
    fn rvalue(&mut self, e: &Expr) -> Result<String, String> {
        match &e.val {
            ExprT::VAttr(_, inner) => self.rvalue(inner),
            ExprT::Var(v) => {
                if let Some(s) = self.slots.iter().rev().find(|s| s.name == *v.val) {
                    if !s.init {
                        return Err(format!("`{}` is read before it is written", v.val));
                    }
                    let ty = self.ty_of(e)?;
                    let pn = palow_name(self.tds, &ty)
                        .ok_or_else(|| format!("`{}` has an unsupported type", v.val))?;
                    let t = self.fresh(&v.val);
                    self.lines
                        .push(format!("let {} = {}_read loc_{};", t, pn, v.val));
                    Ok(t)
                } else if self.env.lookup_var(v).is_some() {
                    Ok(format!("var_{}", v.val))
                } else {
                    // A global: it has storage, and translating it means
                    // deciding who owns it. Milestone 2 does not cover that.
                    Err(format!("`{}` is a global", v.val))
                }
            }
            ExprT::Deref(inner) => {
                if let ExprT::Var(v) = &inner.val {
                    if self.out_params.iter().any(|n| *n == *v.val) {
                        return Err(format!("`*{}` is read before it is written", v.val));
                    }
                }
                let ty = self.ty_of(e)?;
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("a dereference yields {}", describe(&ty)))?;
                let a = self.addr(e)?;
                let t = self.fresh("deref");
                self.lines.push(format!("let {} = {}_read {};", t, pn, a));
                Ok(t)
            }
            ExprT::BoolLit(b) => Ok(if *b { "true" } else { "false" }.to_string()),
            ExprT::IntLit(n, ty) => int_literal(self.tds, n, ty),
            ExprT::Cast(inner, to) => {
                let from = self.ty_of(inner)?;
                if fstar_type(self.tds, &from) == fstar_type(self.tds, to) {
                    return self.rvalue(inner);
                }
                let v = self.rvalue(inner)?;
                convert(self.tds.resolve(&from), self.tds.resolve(to), &v)
            }
            ExprT::BinOp(op, l, r) => {
                let ty = self.ty_of(l)?;
                let opstr = binop(self.tds, *op, &ty, self.signed_ok)?;
                let a = self.rvalue(l)?;
                let b = self.rvalue(r)?;
                Ok(format!("({} {} {})", a, opstr, b))
            }
            ExprT::UnOp(UnOp::Not, inner) => {
                let a = self.rvalue(inner)?;
                Ok(format!("(not {})", a))
            }
            ExprT::Ref(inner) => self.addr(inner),
            ExprT::FnCall(name, args) => {
                let t = self.fresh(&name.val);
                let call = self.call(name, args)?;
                self.lines.push(format!("let {} = {};", t, call));
                Ok(t)
            }
            ExprT::SizeOf(t) => {
                let n = palow_sizeof(self.tds, t)
                    .ok_or_else(|| format!("`sizeof` of {}", describe(self.tds.resolve(t))))?;
                Ok(format!("{}sz", n))
            }
            ExprT::AlignOf(t) => {
                let n = palow_alignof(self.tds, t)
                    .ok_or_else(|| format!("`_Alignof` of {}", describe(self.tds.resolve(t))))?;
                Ok(format!("{}sz", n))
            }
            _ => Err(format!("{} is not translated yet", expr_kind(e))),
        }
    }

    /// The F* application for a call to an already-emitted function. Every
    /// argument is translated first, since translating one may emit reads.
    fn call(&mut self, name: &Ident, args: &Exprs) -> Result<String, String> {
        let c = self
            .callees
            .get(&*name.val.to_string())
            .ok_or_else(|| format!("`{}` is not declared earlier in this file", name.val))?;
        if !c.simple {
            return Err(format!(
                "`{}` takes ownership the caller cannot pass",
                name.val
            ));
        }
        if !c.contract && self.has_contract {
            return Err(format!("`{}`'s contract was dropped", name.val));
        }
        let mut out = format!("func_{}", name.val);
        for a in args.iter() {
            let v = self.rvalue(a)?;
            out += &format!(" {}", v);
        }
        if args.is_empty() {
            out += " ()";
        }
        Ok(format!("({})", out))
    }

    fn alloc_slot(&mut self, name: &Ident, ty: &Type) -> Result<String, String> {
        let pn = palow_name(self.tds, ty)
            .ok_or_else(|| format!("local `{}` is {}", name.val, describe(self.tds.resolve(ty))))?;
        self.lines
            .push(format!("let loc_{} = {}_stack_alloc ();", name.val, pn));
        self.slots.push(Slot {
            name: name.val.to_string(),
            palow_ty: pn.clone(),
            init: false,
        });
        Ok(pn)
    }

    /// Store into an lvalue, choosing the initialising store when the target
    /// is a slot that has not been written yet.
    fn store(&mut self, lhs: &Expr, pn: &str, value: &str) -> Result<(), String> {
        if let ExprT::Deref(inner) = &lhs.val {
            if let ExprT::Var(v) = &inner.val {
                if let Some(i) = self.out_params.iter().position(|n| *n == *v.val) {
                    self.out_params.remove(i);
                    self.lines
                        .push(format!("{}_write_uninit var_{} {};", pn, v.val, value));
                    return Ok(());
                }
            }
        }
        if let ExprT::Var(v) = &lhs.val {
            if let Some(i) = self.slots.iter().rposition(|s| s.name == *v.val) {
                let op = if self.slots[i].init {
                    "write"
                } else {
                    "write_uninit"
                };
                self.slots[i].init = true;
                self.lines
                    .push(format!("{}_{} loc_{} {};", pn, op, v.val, value));
                return Ok(());
            }
        }
        let a = self.addr(lhs)?;
        self.lines.push(format!("{}_write {} {};", pn, a, value));
        Ok(())
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        match &s.val {
            StmtT::Decl(name, ty) => {
                self.alloc_slot(name, ty)?;
                Ok(())
            }
            StmtT::Let(name, ty, init) => {
                let v = self.rvalue(init)?;
                let pn = self.alloc_slot(name, ty)?;
                self.lines
                    .push(format!("{}_write_uninit loc_{} {};", pn, name.val, v));
                self.slots.last_mut().unwrap().init = true;
                Ok(())
            }
            StmtT::Assign(lhs, rhs) => {
                let ty = self.ty_of(lhs)?;
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("an assignment to {}", describe(&ty)))?;
                let v = self.rvalue(rhs)?;
                self.store(lhs, &pn, &v)
            }
            StmtT::Return(None) => Ok(()),
            StmtT::Call(e) => match &e.val {
                ExprT::FnCall(name, args) => {
                    let void = self
                        .callees
                        .get(&*name.val.to_string())
                        .is_some_and(|c| c.void);
                    let call = self.call(name, args)?;
                    if void {
                        self.lines.push(format!("{};", call));
                    } else {
                        let t = self.fresh(&name.val);
                        self.lines.push(format!("let {} = {};", t, call));
                    }
                    Ok(())
                }
                _ => Err("a call through a function pointer".to_string()),
            },
            StmtT::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                // The `_ensures` PAL requires on an `if` today is not
                // translated, and does not need to be: Pulse computes the join
                // itself from the two branches, so the annotation exists only
                // to be checked, not to make the code typecheck.
                let cty = self.ty_of(cond)?;
                if !matches!(self.tds.resolve(&cty).val, TypeT::Bool) {
                    return Err("an `if` on a non-boolean condition".to_string());
                }
                let c = self.rvalue(cond)?;

                // Whether a slot holds a value or still holds uninitialised
                // storage decides which of two *different* slprops it has, and
                // that is the one thing Pulse cannot join for us. The two arms
                // therefore have to agree, which is a real restriction on the
                // C we accept rather than an artefact: an `if` that
                // initialises a local on one path only genuinely leaves two
                // different states behind.
                //
                // Both arms start from the state at the `if`, so the second is
                // translated against a restored snapshot rather than against
                // whatever the first left behind.
                let entry_out = self.out_params.clone();
                let entry_inits: Vec<bool> = self.slots.iter().map(|s| s.init).collect();
                let then = self.branch(then_branch)?;
                self.out_params = entry_out;
                for (slot, init) in self.slots.iter_mut().zip(&entry_inits) {
                    slot.init = *init;
                }
                let els = self.branch(else_branch)?;
                if then.inits != els.inits || then.out_params != els.out_params {
                    return Err(
                        "an `if` whose branches leave different variables initialised".to_string(),
                    );
                }
                self.out_params = then.out_params.clone();
                for (slot, init) in self.slots.iter_mut().zip(&then.inits) {
                    slot.init = *init;
                }

                self.lines.push(format!("if ({})", c));
                self.lines.push("{".to_string());
                self.lines.extend(then.lines.iter().map(|l| indent(l)));
                self.lines.push("} else {".to_string());
                self.lines.extend(els.lines.iter().map(|l| indent(l)));
                self.lines.push("};".to_string());
                Ok(())
            }
            _ => Err(format!("{} is not translated yet", stmt_kind(s))),
        }
    }

    /// Translate one arm of an `if` into its own line buffer. The arm is a C
    /// block, so the locals it declares are released at its end and its
    /// declarations do not escape; what does escape is which of the
    /// *enclosing* slots it left initialised, which is what the two arms have
    /// to agree on.
    fn branch(&mut self, stmts: &Stmts) -> Result<BranchResult, String> {
        let mark = self.slots.len();
        let outer_env = self.env.clone();
        let outer_lines = std::mem::take(&mut self.lines);
        let outer_out = self.out_params.clone();

        let result = (|| -> Result<(), String> {
            for s in stmts.iter() {
                if matches!(s.val, StmtT::Return(_)) {
                    return Err("a `return` inside an `if`".to_string());
                }
                self.env.push_stmt(s);
                self.stmt(s)?;
            }
            Ok(())
        })();

        let out = (|| {
            result?;
            self.release_from(mark);
            Ok(BranchResult {
                lines: std::mem::take(&mut self.lines),
                inits: self.slots[..mark].iter().map(|s| s.init).collect(),
                out_params: std::mem::take(&mut self.out_params),
            })
        })();

        self.slots.truncate(mark);
        self.env = outer_env;
        self.lines = outer_lines;
        if out.is_err() {
            self.out_params = outer_out;
        }
        out
    }

    /// Release every slot, innermost first. A slot holding a value needs
    /// `_forget` first, because deallocation must not depend on what was last
    /// stored in it.
    fn release(&mut self) {
        self.release_from(0);
    }

    fn release_from(&mut self, mark: usize) {
        for i in (mark..self.slots.len()).rev() {
            let (name, pn, init) = {
                let s = &self.slots[i];
                (s.name.clone(), s.palow_ty.clone(), s.init)
            };
            if init {
                self.lines.push(format!("{}_forget loc_{};", pn, name));
            }
            self.lines.push(format!("{}_stack_free loc_{};", pn, name));
        }
    }
}

fn int_literal(tds: &Typedefs, n: &BigInt, ty: &Type) -> Result<String, String> {
    match &tds.resolve(ty).val {
        TypeT::Int { signed, width } => {
            let suffix = int_suffix(*signed, *width)?;
            if *n < BigInt::ZERO {
                if !*signed {
                    // The literal has already been reduced mod 2^width in C;
                    // reproducing that here is easy but pointless until the
                    // arithmetic that consumes it is translated.
                    return Err("a negative literal at unsigned type".to_string());
                }
                Ok(format!("({}{})", n, suffix))
            } else {
                Ok(format!("{}{}", n, suffix))
            }
        }
        TypeT::SizeT => Ok(format!("{}sz", n)),
        _ => Err("an integer literal of an unsupported type".to_string()),
    }
}

/// A C scalar conversion. The integer cases go through `FStar.Int.Cast`,
/// which is total and reduces modulo the target width -- what C says for an
/// unsigned target, and what PAL already emits for every narrowing cast.
fn convert(from: &Type, to: &Type, v: &str) -> Result<String, String> {
    let name = |signed: bool, width: u32| format!("{}int{}", if signed { "" } else { "u" }, width);
    match (&from.val, &to.val) {
        (
            TypeT::Int {
                signed: s1,
                width: w1,
            },
            TypeT::Int {
                signed: s2,
                width: w2,
            },
        ) => Ok(format!(
            "(FStar.Int.Cast.{}_to_{} {})",
            name(*s1, *w1),
            name(*s2, *w2),
            v
        )),
        // C's `_Bool` converts to 0 or 1, and back by comparison with zero.
        (TypeT::Bool, TypeT::Int { signed, width }) => {
            let one = int_suffix(*signed, *width)?;
            Ok(format!("(if {} then 1{} else 0{})", v, one, one))
        }
        (TypeT::Int { signed, width }, TypeT::Bool) => {
            let z = int_suffix(*signed, *width)?;
            let m = format!("{}Int{}", if *signed { "" } else { "U" }, width);
            Ok(format!("(not ({} `{}.eq` 0{}))", v, m, z))
        }
        _ => Err(format!(
            "a conversion from {} to {}",
            describe(from),
            describe(to)
        )),
    }
}

fn int_suffix(signed: bool, width: u32) -> Result<&'static str, String> {
    Ok(match (signed, width) {
        (true, 8) => "y",
        (false, 8) => "uy",
        (true, 16) => "s",
        (false, 16) => "us",
        (true, 32) => "l",
        (false, 32) => "ul",
        (true, 64) => "L",
        (false, 64) => "UL",
        _ => return Err("an integer of an unsupported width".to_string()),
    })
}

fn binop(tds: &Typedefs, op: BinOp, ty: &Type, signed_ok: bool) -> Result<String, String> {
    let t = tds.resolve(ty);
    let m = match &t.val {
        TypeT::Int { signed, width } => {
            format!("{}Int{}", if *signed { "" } else { "U" }, width)
        }
        TypeT::SizeT => "SizeT".to_string(),
        TypeT::Bool => {
            return match op {
                BinOp::Eq => Ok("=".to_string()),
                BinOp::LogAnd => Ok("&&".to_string()),
                BinOp::LogOr => Ok("||".to_string()),
                _ => Err("an unsupported boolean operator".to_string()),
            };
        }
        _ => return Err(format!("an operator on {}", describe(t))),
    };
    match op {
        BinOp::Eq => return Ok("=".to_string()),
        BinOp::Lt => return Ok(format!("`{}.lt`", m)),
        BinOp::LEq => return Ok(format!("`{}.lte`", m)),
        _ => {}
    }

    // C's unsigned arithmetic wraps, so it is total and always translatable.
    // Signed arithmetic is undefined on overflow, which PAL turns into a proof
    // obligation, and that obligation is discharged by the function's
    // `_requires` clause. When the contract did not translate, emitting it
    // would produce a failure that says nothing about the memory model, so it
    // is refused instead.
    if let TypeT::Int {
        signed: false,
        width,
    } = &t.val
    {
        let wrap = format!("Pulse.Lib.C.UInt{}", width);
        return Ok(match op {
            BinOp::Add => format!("`{}.add_wrap`", wrap),
            BinOp::Sub => format!("`{}.sub_wrap`", wrap),
            BinOp::Mul => format!("`{}.mul_wrap`", wrap),
            BinOp::Div => format!("`{}.div`", m),
            BinOp::Mod => format!("`{}.rem`", m),
            _ => return Err("an unsupported operator".to_string()),
        });
    }
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul if !signed_ok => Err(
            "signed arithmetic, whose overflow obligation needs the untranslated `_requires`"
                .to_string(),
        ),
        BinOp::Add => Ok(format!("`{}.add`", m)),
        BinOp::Sub => Ok(format!("`{}.sub`", m)),
        BinOp::Mul => Ok(format!("`{}.mul`", m)),
        BinOp::Div => Ok(format!("`{}.div`", m)),
        BinOp::Mod => Ok(format!("`{}.rem`", m)),
        _ => Err("an unsupported operator".to_string()),
    }
}

/// Translate a function body, or say why not. `env` must already have the
/// function's parameters pushed.
fn emit_body(
    tds: &Typedefs,
    env: Env,
    defn: &FnDefn,
    sig: &FnSurface,
    callees: &HashMap<String, Callee>,
) -> Result<Vec<String>, String> {
    // An array parameter's ownership is a sequence, so every access through it
    // needs `array_focus` rather than a plain read. The contract already says
    // so; the body translation does not do it yet.
    if defn
        .decl
        .args
        .iter()
        .any(|a| extent(tds, &a.ty) == Some(Extent::Array))
    {
        return Err("an array parameter".to_string());
    }

    let mut b = Body {
        tds,
        env,
        callees,
        lines: Vec::new(),
        slots: Vec::new(),
        out_params: defn
            .decl
            .args
            .iter()
            .filter(|a| a.mode == ParamMode::Out)
            .filter_map(|a| a.name.as_ref().map(|n| n.val.to_string()))
            .collect(),
        tmp: 0,
        signed_ok: sig.contract,
        has_contract: !defn.decl.ensures.is_empty(),
    };

    // Straight-line bodies only, with an optional trailing `return`. A
    // `return` anywhere else would have to release the slots on that path too,
    // which is a restructuring rather than a translation.
    let (last, init) = match defn.body.split_last() {
        Some((l, i)) => (Some(l), i),
        None => (None, &defn.body[..]),
    };
    for s in init {
        if matches!(s.val, StmtT::Return(_)) {
            return Err("an early return".to_string());
        }
        b.env.push_stmt(s);
        b.stmt(s)?;
    }

    let mut tail = None;
    if let Some(l) = last {
        match &l.val {
            StmtT::Return(Some(e)) => {
                tail = Some(b.rvalue(e)?);
            }
            _ => {
                b.env.push_stmt(l);
                b.stmt(l)?;
            }
        }
    }

    b.release();
    if let Some(t) = tail {
        b.lines.push(t);
    }
    Ok(b.lines)
}

/// Names for the constructs the subset does not cover. These end up in the
/// generated file next to each `admit()`, which is what turns it into a list
/// of what to do next rather than a list of failures.
fn stmt_kind(s: &Stmt) -> &'static str {
    match &s.val {
        StmtT::Call(..) => "a function call",
        StmtT::If { .. } => "an `if`",
        StmtT::Match { .. } => "a `switch`",
        StmtT::While { .. } => "a loop",
        StmtT::Break => "a `break`",
        StmtT::Continue => "a `continue`",
        StmtT::Return(..) => "a non-tail `return`",
        StmtT::Assert(..) => "an assertion",
        StmtT::GhostStmt(..) => "inline Pulse",
        StmtT::Goto(..) | StmtT::Label { .. } | StmtT::GotoBlock { .. } => "a `goto`",
        StmtT::DeclStackArray { .. } => "a stack array",
        StmtT::Error => "an ill-formed statement",
        StmtT::Decl(..) | StmtT::Let(..) | StmtT::Assign(..) => "this statement",
    }
}

fn expr_kind(e: &Expr) -> &'static str {
    match &e.val {
        ExprT::Member(..) => "a struct field access",
        ExprT::Index(..) => "an array subscript",
        ExprT::Ref(..) => "an address-of",
        ExprT::FnCall(..) => "a function call",
        ExprT::FnRef(..) | ExprT::FnPtrCall(..) => "a function pointer",
        ExprT::Cond(..) => "a conditional expression",
        ExprT::PreIncr(..) | ExprT::PostIncr(..) | ExprT::PreDecr(..) | ExprT::PostDecr(..) => {
            "an increment or decrement"
        }
        ExprT::AssignExpr(..) => "an assignment expression",
        ExprT::Malloc(..)
        | ExprT::MallocArray(..)
        | ExprT::MallocFlex(..)
        | ExprT::Calloc(..)
        | ExprT::CallocArray(..)
        | ExprT::CallocFlex(..)
        | ExprT::Free(..) => "an allocation",
        ExprT::Memset(..) | ExprT::MemsetZero(..) => "a `memset`",
        ExprT::SizeOf(..) | ExprT::AlignOf(..) => "a `sizeof`",
        ExprT::StructInit(..) | ExprT::UnionInit(..) | ExprT::ArrayInit { .. } => {
            "an initialiser list"
        }
        ExprT::FloatLit(..) => "a float literal",
        ExprT::UnOp(..) => "a unary operator",
        ExprT::ContainerOf(..) => "`_container_of`",
        ExprT::InlinePulse(..) => "inline Pulse",
        ExprT::Live(..) | ExprT::Old(..) | ExprT::Forall(..) | ExprT::Exists(..) => {
            "a specification construct"
        }
        _ => "this expression",
    }
}
