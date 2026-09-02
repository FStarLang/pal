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
/// One field of a struct the emitter generated a type for.
struct StructField {
    /// The C field name.
    name: String,
    ty: Rc<Type>,
    /// Byte offset from the start of the struct, per clang's target ABI.
    offset: u64,
    shape: FieldShape,
}

/// How a struct field is owned. A scalar or nested struct field is one
/// points-to; a fixed-size array field is a whole `array_pts_to`, because in C
/// `T f[N]` inside a struct is N elements of storage and not a pointer.
enum FieldShape {
    One { pn: String },
    Array { pn: String, esize: u64, len: u64 },
}

impl FieldShape {
    /// The F* type of the field's value. An array field's length is part of
    /// the type rather than a side condition, so that `Seq.upd` through it
    /// obviously preserves it.
    fn value_type(&self, elem: &str) -> String {
        match self {
            FieldShape::One { .. } => elem.to_string(),
            FieldShape::Array { len, .. } => {
                format!("(s: Seq.seq {} {{ Seq.length s == {} }})", elem, len)
            }
        }
    }

    fn pts_to(&self, at: &str, value: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_pts_to {} p {}", pn, at, value),
            FieldShape::Array { pn, esize, .. } => {
                format!("array_pts_to {}_repr {} {} p {}", pn, esize, at, value)
            }
        }
    }
}

/// How a struct field is owned, or `None` if the model does not cover it.
fn field_shape(tds: &Typedefs, ty: &Type) -> Option<FieldShape> {
    match &tds.resolve(ty).val {
        TypeT::FixedArray(t, n) => {
            if !has_repr(tds, t) {
                return None;
            }
            Some(FieldShape::Array {
                pn: palow_name(tds, t)?,
                esize: palow_sizeof(tds, t)?,
                len: *n,
            })
        }
        _ => Some(FieldShape::One {
            pn: palow_name(tds, ty)?,
        }),
    }
}

/// The F* type of a struct field's value.
fn field_type(tds: &Typedefs, ty: &Type) -> Option<String> {
    let elem = match &tds.resolve(ty).val {
        TypeT::FixedArray(t, _) => fstar_type(tds, t)?,
        _ => fstar_type(tds, ty)?,
    };
    Some(field_shape(tds, ty)?.value_type(&elem))
}

/// A struct the emitter generated a Palow type for. Only structs whose every
/// field has a Palow type get one; the rest stay unknown and any function that
/// mentions them is skipped, as before.
struct StructInfo {
    fields: Vec<StructField>,
    size: u64,
    align: u64,
}

struct Typedefs<'a> {
    typedefs: HashMap<&'a str, &'a Rc<Type>>,
    structs: HashMap<String, StructInfo>,
}

impl<'a> Typedefs<'a> {
    fn new(tu: &'a TranslationUnit) -> Self {
        let mut m = HashMap::new();
        for decl in &tu.decls {
            if let DeclT::Typedef(td) = &decl.val {
                m.insert(&*td.name.val, &td.body);
            }
        }
        Typedefs {
            typedefs: m,
            structs: HashMap::new(),
        }
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
                TypeT::TypeRef(TypeRefKind::Typedef(n)) => match self.typedefs.get(&*n.val) {
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
/// The F* module whose `v` takes a machine integer to a mathematical one.
fn int_module(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &tds.resolve(ty).val {
        TypeT::Int { signed, width } => {
            Some(format!("{}Int{}", if *signed { "" } else { "U" }, width))
        }
        TypeT::SizeT => Some("SizeT".to_string()),
        _ => None,
    }
}

fn palow_name(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &tds.resolve(ty).val {
        TypeT::Bool => Some("bool_t".to_string()),
        TypeT::Int { signed, width } => {
            Some(format!("{}int{}_t", if *signed { "" } else { "u" }, width))
        }
        TypeT::SizeT => Some("size_t".to_string()),
        // Every pointer kind is the same type here; that is the point.
        TypeT::Pointer(..) => Some("ptr".to_string()),
        TypeT::TypeRef(TypeRefKind::Struct(n)) if tds.structs.contains_key(&*n.val) => {
            Some(format!("struct_{}", n.val))
        }
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
        TypeT::TypeRef(TypeRefKind::Struct(n)) if tds.structs.contains_key(&*n.val) => {
            Some(format!("struct_{}", n.val))
        }
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => fstar_type(tds, t),
        _ => None,
    }
}

/// Whether a type has a byte-level `_repr` relation. Every scalar does; a
/// generated struct does not, because its points-to is defined as the
/// conjunction of its fields' rather than over its bytes. Arrays are indexed by
/// `_repr`, so this is what an array's element type has to satisfy.
fn has_repr(tds: &Typedefs, ty: &Type) -> bool {
    palow_name(tds, ty).is_some()
        && !matches!(
            tds.resolve(ty).val,
            TypeT::TypeRef(TypeRefKind::Struct(_)) | TypeT::TypeRef(TypeRefKind::Union(_))
        )
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
        TypeT::TypeRef(TypeRefKind::Struct(n)) => tds.structs.get(&*n.val).map(|s| s.size),
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
        TypeT::TypeRef(TypeRefKind::Struct(n)) => tds.structs.get(&*n.val).map(|s| s.align),
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
        int_module(self.tds, ty)
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
                        // A literal written at specification level and cast to
                        // a machine type -- which is what `a[0]` elaborates to
                        // -- is just that literal at that type.
                        if let (ExprT::IntLit(n, _), TypeT::SpecInt | TypeT::SpecNat) =
                            (&inner.val, &self.tds.resolve(&from).val)
                        {
                            return int_literal(self.tds, n, to);
                        }
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
            ExprT::Index(base, idx) if matches!(strip_vattr(base).val, ExprT::Var(_)) => {
                self.pointee_at(base, Some(idx), w)
            }
            // A fixed-size array *field* is a sequence in the struct's record,
            // so indexing it is `Seq.index` of a projection rather than a
            // lookup in a parameter's own sequence.
            ExprT::Index(base, idx) => {
                let bty = self.ty_of(base)?;
                if !matches!(self.tds.resolve(&bty).val, TypeT::FixedArray(..)) {
                    return Err(format!(
                        "a contract that indexes {}",
                        describe(self.tds.resolve(&bty))
                    ));
                }
                let seq = self.value(base, w)?;
                let i = self.num(idx, w)?;
                self.guards
                    .borrow_mut()
                    .push(format!("{} < Seq.length {}", i, seq));
                Ok(format!("(Seq.index {} {})", seq, i))
            }
            // A struct value is an F* record, so a field of one is a
            // projection. `s->f` reaches here as `(*s).f`.
            ExprT::Member(base, f) => {
                let bty = self.ty_of(base)?;
                if palow_name(self.tds, &bty).is_none() {
                    return Err(format!(
                        "a contract that projects a field of {}",
                        describe(self.tds.resolve(&bty))
                    ));
                }
                Ok(format!("({}).fld_{}", self.value(base, w)?, f.val))
            }
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
                    if !has_repr(tds, pt) {
                        return Err(format!(
                            "parameter {} is an array of {}, which has no byte-level `_repr`",
                            pname,
                            describe(tds.resolve(pt))
                        ));
                    }
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

/// Generate the Palow type for every struct in the translation unit whose
/// fields the model covers, and the code that goes with it.
///
/// The shape is a deliberate departure from the byte-level definition in
/// `Pulse.Lib.C.Palow.Aggregate`. There a struct's points-to is one
/// `mem_pts_to` over the whole object with a `_repr` relating it to the field
/// values, and the split is a chain of `mem_split`s plus enough `slice`
/// reasoning to line the pieces up. That definition is the right one for
/// reasoning about representation -- type punning needs it -- but it is the
/// wrong one to generate, because every field access would carry that proof.
///
/// Here `struct_S_pts_to` is instead defined *as* the separating conjunction of
/// its fields' points-to predicates, so the split and the join are an `unfold`
/// and a `fold` and always go through. The byte-level view is still reachable:
/// each field's own `t_reveal` produces its bytes and `mem_join` puts them back
/// together. It is reachable deliberately rather than by default, which is the
/// same principle the scalar layer follows.
///
/// What this shape does not say is anything about padding. A struct's ownership
/// here is the ownership of its fields, not of its bytes, so it is short of the
/// whole object by however many padding bytes clang inserted. That is fine for
/// field access, which is all the translator does with it, and it is what a
/// whole-object `memcpy` or `free` would need a bridge lemma for.
fn collect_structs(tu: &TranslationUnit, tds: &mut Typedefs) -> String {
    let layouts = crate::layout::LayoutCtx::of_tu(tu);
    let mut code = String::new();
    for decl in &tu.decls {
        let DeclT::StructDefn(sd) = &decl.val else {
            continue;
        };
        let name = sd.name.val.to_string();
        let key = TypeRefKind::Struct(sd.name.clone());
        let (Some(size), Some(align)) = (
            layouts
                .table
                .get(&LayoutKey::of_type_ref(&key))
                .map(|l| l.size),
            layouts
                .table
                .get(&LayoutKey::of_type_ref(&key))
                .map(|l| l.align),
        ) else {
            continue;
        };
        // Every field has to have a Palow type. Structs are processed in
        // declaration order, so a field of an earlier struct type works and a
        // field of a later one does not -- which is also all C allows.
        let mut fields = Vec::new();
        let mut ok = true;
        let mut bad = String::new();
        for f in &sd.fields {
            let fname = f.val.name().val.to_string();
            let fty = f.val.logical_type(&f.loc);
            let (Some(off), Some(shape), true) = (
                layouts.offset_of(&key, &fname),
                field_shape(tds, &fty),
                field_type(tds, &fty).is_some(),
            ) else {
                ok = false;
                bad = match layouts.offset_of(&key, &fname) {
                    // Bit-fields have no byte offset, and the model has no
                    // sub-byte addressing to give them one.
                    None => format!("field `{}` has no byte offset", fname),
                    Some(_) => format!("field `{}` is {}", fname, describe(tds.resolve(&fty))),
                };
                break;
            };
            fields.push(StructField {
                name: fname,
                ty: fty,
                offset: off,
                shape,
            });
        }
        if !ok || fields.is_empty() {
            if bad.is_empty() {
                bad = "it has no fields".to_string();
            }
            code += &format!("(* skipped struct {}: {} *)\n\n", name, bad);
            continue;
        }
        tds.structs.insert(
            name.clone(),
            StructInfo {
                fields,
                size,
                align,
            },
        );
        code += &emit_struct(tds, &name);
    }
    code
}

/// The generated code for one struct: the record, its layout constants, its
/// points-to, and per field a hole predicate with the focus/unfocus pair that
/// opens and closes it. The per-field triple is the same shape as the array
/// combinator's, on purpose: a field access and a subscript are the same
/// operation on a sub-range, and the emitter should not have to tell them
/// apart.
fn emit_struct(tds: &Typedefs, name: &str) -> String {
    let si = &tds.structs[name];
    let sn = format!("struct_{}", name);
    let mut c = String::new();

    c += &format!(
        "noeq type {} = {{ {} }}\n\n",
        sn,
        si.fields
            .iter()
            .map(|f| format!("fld_{}: {}", f.name, field_type(tds, &f.ty).unwrap()))
            .collect::<Vec<_>>()
            .join("; ")
    );
    c += &format!("let {}_sizeof : SizeT.t = {}sz\n", sn, si.size);
    c += &format!("let {}_alignof : SizeT.t = {}sz\n", sn, si.align);
    for f in &si.fields {
        c += &format!(
            "let {}_offsetof_{} : SizeT.t = {}sz\n",
            sn, f.name, f.offset
        );
    }
    c += "\n";

    // The field points-to at a given record expression, for every field but
    // one; `None` excludes nothing.
    let conj = |x: &str, skip: Option<&str>| -> String {
        let parts: Vec<String> = si
            .fields
            .iter()
            .filter(|f| Some(f.name.as_str()) != skip)
            .map(|f| {
                f.shape.pts_to(
                    &format!("(a +! {}_offsetof_{})", sn, f.name),
                    &format!("({}).fld_{}", x, f.name),
                )
            })
            .collect();
        if parts.is_empty() {
            "emp".to_string()
        } else {
            parts.join(" **\n  ")
        }
    };

    c += &format!(
        "let {}_pts_to ([@@@mkey] a: ptr) (p: perm) (x: {}) : slprop =\n  {}\n\n",
        sn,
        sn,
        conj("x", None)
    );

    for f in &si.fields {
        let fty = field_type(tds, &f.ty).unwrap();
        let at = format!("(a +! {}_offsetof_{})", sn, f.name);
        let upd = format!("({{ x with fld_{} = y }})", f.name);
        let owned = |v: &str| f.shape.pts_to(&at, v);
        c += &format!(
            "let {}_hole_{} (a: ptr) (p: perm) (x: {}) : slprop =\n  {}\n\n",
            sn,
            f.name,
            sn,
            conj("x", Some(&f.name))
        );
        c += &format!(
            "ghost fn {sn}_focus_{f} (a: ptr) (#p: perm) (#x: {sn})\n\
             \x20 requires {sn}_pts_to a p x\n\
             \x20 ensures  {owned}\n\
             \x20 ensures  {sn}_hole_{f} a p x\n\
             {{\n  unfold {sn}_pts_to a p x;\n  fold {sn}_hole_{f} a p x;\n}}\n\n",
            sn = sn,
            f = f.name,
            owned = owned(&format!("x.fld_{}", f.name))
        );
        c += &format!(
            "ghost fn {sn}_unfocus_{f} (a: ptr) (#p: perm) (#x: {sn}) (#y: {fty})\n\
             \x20 requires {sn}_hole_{f} a p x\n\
             \x20 requires {owned}\n\
             \x20 ensures  {sn}_pts_to a p {upd}\n\
             {{\n  unfold {sn}_hole_{f} a p x;\n  fold {sn}_pts_to a p {upd};\n}}\n\n",
            sn = sn,
            f = f.name,
            fty = fty,
            owned = owned("y"),
            upd = upd
        );
        c += &format!(
            "ghost fn {sn}_unfocus_read_{f} (a: ptr) (#p: perm) (#x: {sn})\n\
             \x20 requires {sn}_hole_{f} a p x\n\
             \x20 requires {owned}\n\
             \x20 ensures  {sn}_pts_to a p x\n\
             {{\n  unfold {sn}_hole_{f} a p x;\n  fold {sn}_pts_to a p x;\n}}\n\n",
            sn = sn,
            f = f.name,
            owned = owned(&format!("x.fld_{}", f.name))
        );
    }
    c
}

pub fn emit_palow(tu: &TranslationUnit) -> Vec<PalowModule> {
    let mut tds = Typedefs::new(tu);
    let structs = collect_structs(tu, &mut tds);
    let tds = tds;
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
    code += &structs;

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
#[derive(Clone)]
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
    /// Whether we are translating the arm of an `if`, where a slot introduced
    /// now would not outlive the arm.
    in_branch: bool,
    /// Array-kind pointer parameters, by C name.
    arrays: HashMap<String, ArrayParam>,
    /// The function's parameters, by C name. Ownership of what a pointer points
    /// to is granted by the contract, and the contract only names parameters.
    params: HashSet<String>,
    /// Whether the function has a translated `_requires`. Bounds and overflow
    /// obligations are discharged by it, so without one there is nothing to
    /// discharge them with.
    requires_ok: bool,
}

/// What a subscript through an array parameter needs: the element's Palow type
/// name, and its size as a `size_t` literal.
struct ArrayParam {
    pn: String,
    esize: String,
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
                    return Ok(format!("loc_{}", v.val));
                }
                // A C parameter is an ordinary mutable object; Palow passes it
                // by value, so it only acquires storage if the body asks for
                // it. It does here, so give it a slot now and copy the
                // incoming value in. Every later mention goes through the slot
                // because the slot lookup comes first.
                if self.env.lookup_var(v).is_none() {
                    return Err(format!("`{}` is a global", v.val));
                }
                if self.in_branch {
                    // The slot would be scoped to the arm, but uses of the
                    // parameter after the `if` would still read the value that
                    // was passed in.
                    return Err(format!("`{}` is addressed inside an `if`", v.val));
                }
                let ty = self.ty_of(e)?;
                if !has_repr(self.tds, &ty) {
                    return Err(format!(
                        "`{}` is {}",
                        v.val,
                        describe(self.tds.resolve(&ty))
                    ));
                }
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("`{}` has an unsupported type", v.val))?;
                self.lines
                    .push(format!("let loc_{} = {}_stack_alloc ();", v.val, pn));
                self.lines
                    .push(format!("{}_write_uninit loc_{} var_{};", pn, v.val, v.val));
                self.slots.push(Slot {
                    name: v.val.to_string(),
                    palow_ty: pn,
                    init: true,
                });
                Ok(format!("loc_{}", v.val))
            }
            // The address of `*e` is the value of `e`, but only ownership we
            // can name is ownership we have. A parameter or a local carries its
            // pointee in the contract; a pointer that was itself loaded out of
            // memory -- `*s->next`, `**p` -- does not, and the caller would
            // have had to grant it in a `_requires` that is not translated.
            ExprT::Deref(inner) => match &strip_vattr(inner).val {
                ExprT::Var(v) if self.params.contains(&*v.val.to_string()) => self.rvalue(inner),
                ExprT::Var(v) => Err(format!(
                    "a dereference of local `{}`, whose target the contract does not grant",
                    v.val
                )),
                other => Err(format!(
                    "a dereference of {}, whose target the contract does not grant",
                    expr_kind_of(other)
                )),
            },
            ExprT::VAttr(_, inner) => self.addr(inner),
            _ => Err("unsupported lvalue".to_string()),
        }
    }

    /// The index of a subscript, as a `size_t`. C allows any integer type
    /// here; a signed one would need `i >= 0` to convert, which is exactly the
    /// obligation the dropped `_requires` would have carried.
    fn index(&mut self, e: &Expr) -> Result<String, String> {
        let ty = self.ty_of(e)?;
        let v = self.rvalue(e)?;
        match &self.tds.resolve(&ty).val {
            TypeT::SizeT => Ok(v),
            TypeT::Int {
                signed: false,
                width,
            } if *width != 8 => Ok(format!("(sizet_of_uint{} {})", width, v)),
            _ => Err(format!("a subscript indexed by {}", describe(&ty))),
        }
    }

    /// Open one element of an array parameter for a single access. Emits the
    /// prologue -- the offset's `fits` fact, the focus, and the trade from the
    /// generic element predicate into the type's own -- and returns the
    /// element's address together with what the epilogue needs.
    ///
    /// The caller must emit the matching `unfocus` immediately after the read
    /// or write, with nothing in between: the array is in pieces until then.
    fn focus(
        &mut self,
        base: &Expr,
        idx: Option<&Expr>,
    ) -> Result<(String, String, String), String> {
        let ExprT::Var(v) = &base.val else {
            return Err("a subscript of a computed pointer".to_string());
        };
        let Some(ap) = self.arrays.get(&*v.val.to_string()) else {
            return Err(format!(
                "a subscript of `{}`, which is not an array parameter",
                v.val
            ));
        };
        let (pn, esize) = (ap.pn.clone(), ap.esize.clone());
        // `array_focus` demands `i < Seq.length xs`, which only the function's
        // own `_requires` can supply.
        if !self.signed_ok {
            return Err(
                "a subscript, whose bounds obligation needs the untranslated `_requires`"
                    .to_string(),
            );
        }
        let i = match idx {
            Some(e) => self.index(e)?,
            None => "0sz".to_string(),
        };
        let arr = format!("var_{}", v.val);
        let off = format!("({} `SizeT.mul` {})", esize, i);
        let at = format!("({} +! {})", arr, off);
        self.lines.push(format!(
            "array_offset_fits {}_repr {} {} {};",
            pn, arr, esize, i
        ));
        self.lines.push(format!(
            "array_focus {}_repr {} {} {} {};",
            pn, arr, esize, i, off
        ));
        self.lines.push(format!("{}_of_elem {};", pn, at));
        let close = format!("{} {} {} {}", arr, esize, i, off);
        Ok((at, pn, close))
    }

    /// Open a place -- a field, an array element, or a field's array element --
    /// for a single access, emitting the prologue and returning what closes it.
    ///
    /// A field access and a subscript are the same operation on a sub-range, so
    /// they compose: `s->f[i]` focuses the field, then the element inside it.
    /// The caller emits the closing lines immediately after the read or write,
    /// with nothing in between: the object is in pieces until then.
    fn place(&mut self, e: &Expr) -> Result<Focus, String> {
        match &strip_vattr(e).val {
            ExprT::Member(base, f) => {
                let (sn, at) = self.focus_field(base, f)?;
                Ok(Focus {
                    pn: self.field_pn(base, f)?,
                    at,
                    close_read: vec![format!("{}_unfocus_read_{} {};", sn.0, f.val, sn.1)],
                    close_write: vec![format!("{}_unfocus_{} {};", sn.0, f.val, sn.1)],
                })
            }
            ExprT::Index(base, idx) => self.focus_elem(base, Some(idx)),
            _ => Err(format!("a place that is {}", expr_kind_of(&e.val))),
        }
    }

    /// The struct a field belongs to, if the emitter generated a type for it.
    fn struct_of(&self, base: &Expr) -> Result<(String, Rc<Type>), String> {
        let bty = self.ty_of(base)?;
        let TypeT::TypeRef(TypeRefKind::Struct(sname)) = &self.tds.resolve(&bty).val else {
            return Err(format!("a field of {}", describe(self.tds.resolve(&bty))));
        };
        if !self.tds.structs.contains_key(&*sname.val) {
            return Err(format!("a field of {}", describe(self.tds.resolve(&bty))));
        }
        Ok((format!("struct_{}", sname.val), bty.clone()))
    }

    fn field_ty(&self, base: &Expr, f: &Ident) -> Result<Rc<Type>, String> {
        self.ty_of(&Ast {
            val: ExprT::Member(Rc::new(base.clone()), Rc::new(f.clone())),
            loc: base.loc.clone(),
        })
    }

    fn field_pn(&self, base: &Expr, f: &Ident) -> Result<String, String> {
        let fty = self.field_ty(base, f)?;
        if !has_repr(self.tds, &fty) {
            return Err(format!(
                "a field of type {}",
                describe(self.tds.resolve(&fty))
            ));
        }
        palow_name(self.tds, &fty)
            .ok_or_else(|| format!("a field of type {}", describe(self.tds.resolve(&fty))))
    }

    /// Emit the focus of one field. Returns the struct's Palow name and base
    /// address, and the field's address.
    fn focus_field(
        &mut self,
        base: &Expr,
        f: &Ident,
    ) -> Result<((String, String), String), String> {
        let (sn, _) = self.struct_of(base)?;
        let a = self.addr(base)?;
        let at = format!("({} +! {}_offsetof_{})", a, sn, f.val);
        self.lines.push(format!("{}_focus_{} {};", sn, f.val, a));
        Ok(((sn, a), at))
    }

    /// The array an element access indexes: its base address, element type and
    /// size, and the lines that give it back. Either a parameter, which owns
    /// its sequence outright, or a fixed-size array field, which has to be
    /// focused out of its struct first.
    fn array_place(&mut self, e: &Expr) -> Result<(String, String, String, Vec<String>), String> {
        match &strip_vattr(e).val {
            ExprT::Var(v) => {
                let Some(ap) = self.arrays.get(&*v.val.to_string()) else {
                    return Err(format!(
                        "a subscript of `{}`, which is not an array parameter",
                        v.val
                    ));
                };
                // An array parameter's length is whatever the caller passed, so
                // `i < Seq.length xs` can only come from the function's own
                // `_requires`. An array *field*'s length is part of its type,
                // so it needs no such help -- hence the gate is here and not in
                // `focus_elem`.
                if !self.requires_ok {
                    return Err(
                        "a subscript, whose bounds obligation needs a `_requires` that is not \
                         translated"
                            .to_string(),
                    );
                }
                Ok((
                    format!("var_{}", v.val),
                    ap.pn.clone(),
                    ap.esize.clone(),
                    Vec::new(),
                ))
            }
            ExprT::Member(base, f) => {
                let fty = self.field_ty(base, f)?;
                let Some(FieldShape::Array { pn, esize, .. }) = field_shape(self.tds, &fty) else {
                    return Err(format!(
                        "a subscript of a field of type {}",
                        describe(self.tds.resolve(&fty))
                    ));
                };
                let (sn, at) = self.focus_field(base, f)?;
                // Even a read through an array field goes back with the
                // general unfocus: what comes out of the element access is a
                // sequence, and `Seq.upd xs i (Seq.index xs i)` is only `xs`
                // up to a lemma that is not worth generating per field.
                Ok((
                    at,
                    pn,
                    format!("{}sz", esize),
                    vec![format!("{}_unfocus_{} {};", sn.0, f.val, sn.1)],
                ))
            }
            other => Err(format!("a subscript of {}", expr_kind_of(other))),
        }
    }

    /// Open one element of an array for a single access.
    fn focus_elem(&mut self, base: &Expr, idx: Option<&Expr>) -> Result<Focus, String> {
        let (arr, pn, esize, close) = self.array_place(base)?;
        let i = match idx {
            Some(e) => self.index(e)?,
            None => "0sz".to_string(),
        };
        let off = format!("({} `SizeT.mul` {})", esize, i);
        let at = format!("({} +! {})", arr, off);
        self.lines.push(format!(
            "array_offset_fits {}_repr {} {} {};",
            pn, arr, esize, i
        ));
        self.lines.push(format!(
            "array_focus {}_repr {} {} {} {};",
            pn, arr, esize, i, off
        ));
        self.lines.push(format!("{}_of_elem {};", pn, at));
        let common = format!("{} {} {} {}", arr, esize, i, off);
        let mut close_read = vec![
            format!("{}_to_elem {};", pn, at),
            format!("array_unfocus_read {}_repr {};", pn, common),
        ];
        let mut close_write = vec![
            format!("{}_to_elem {};", pn, at),
            format!("array_unfocus {}_repr {};", pn, common),
        ];
        close_read.extend(close.iter().cloned());
        close_write.extend(close);
        Ok(Focus {
            at,
            pn,
            close_read,
            close_write,
        })
    }

    /// An rvalue, as an F* expression. Reads are effectful, so they are bound
    /// to a fresh name and the binding is pushed onto `lines`.
    /// A specification proposition in *statement* position, as in `_assert`.
    ///
    /// A contract has ghost binders for everything it owns, so it can name a
    /// pointee without touching memory. Inside a body there are no such
    /// binders -- the translator deliberately tracks no values -- so each
    /// mention of an object becomes a real load. That is sound and loses
    /// nothing: a read is the identity on the state, and `rewrites_to` in its
    /// postcondition makes the loaded name definitionally the stored value, so
    /// the assertion Pulse checks is the one the C source wrote.
    fn prop(&mut self, e: &Expr) -> Result<String, String> {
        match &e.val {
            ExprT::VAttr(_, inner) => self.prop(inner),
            ExprT::Cast(inner, to) if matches!(self.tds.resolve(to).val, TypeT::SLProp) => {
                self.prop(inner)
            }
            ExprT::Old(_) => Err("an assertion about the state on entry".to_string()),
            ExprT::UnOp(UnOp::Not, inner) => Ok(format!("(~({}))", self.prop(inner)?)),
            ExprT::BoolLit(b) => Ok(if *b { "True" } else { "False" }.to_string()),
            ExprT::BinOp(op, l, r) => {
                let logical = match op {
                    BinOp::LogAnd => Some("/\\"),
                    BinOp::LogOr => Some("\\/"),
                    BinOp::Implies => Some("==>"),
                    _ => None,
                };
                if let Some(o) = logical {
                    // Both sides are evaluated, because the loads have to
                    // happen before the assertion rather than under it. C's
                    // short-circuiting is invisible here: an assertion has no
                    // side effects, and the loads it needs are exactly the
                    // ones the surrounding ownership already permits.
                    let a = self.prop(l)?;
                    let b = self.prop(r)?;
                    return Ok(format!("({} {} {})", a, o, b));
                }
                let ty = self.ty_of(l)?;
                if matches!(op, BinOp::Eq) {
                    if matches!(self.tds.resolve(&ty).val, TypeT::Bool) {
                        let a = self.prop(l)?;
                        let b = self.prop(r)?;
                        return Ok(format!("({} <==> {})", a, b));
                    }
                    let a = self.num(l)?;
                    let b = self.num(r)?;
                    return Ok(format!("({} == {})", a, b));
                }
                let o = match op {
                    BinOp::Lt => "<",
                    BinOp::LEq => "<=",
                    _ => return Err("an unsupported operator in an assertion".to_string()),
                };
                let a = self.num(l)?;
                let b = self.num(r)?;
                Ok(format!("({} {} {})", a, o, b))
            }
            _ => {
                let ty = self.ty_of(e)?;
                if matches!(self.tds.resolve(&ty).val, TypeT::Bool) {
                    Ok(format!("({} == true)", self.rvalue(e)?))
                } else {
                    Err(format!("{} in an assertion", expr_kind(e)))
                }
            }
        }
    }

    /// A specification expression inside a body, as a mathematical integer.
    fn num(&mut self, e: &Expr) -> Result<String, String> {
        if let ExprT::Cast(inner, to) = &e.val {
            if matches!(self.tds.resolve(to).val, TypeT::SpecInt | TypeT::SpecNat) {
                return self.num(inner);
            }
        }
        let ty = self.ty_of(e)?;
        if matches!(self.tds.resolve(&ty).val, TypeT::SpecInt | TypeT::SpecNat) {
            // Already mathematical: a literal, or an arithmetic expression
            // over specification integers.
            if let ExprT::IntLit(n, _) = &strip_vattr(e).val {
                return Ok(format!("({})", n));
            }
            return Err("a specification computation in an assertion".to_string());
        }
        match int_module(self.tds, &ty) {
            Some(m) => Ok(format!("({}.v {})", m, self.rvalue(e)?)),
            None => self.rvalue(e),
        }
    }

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
                    // `*p` on an array parameter is `p[0]`: the ownership is a
                    // sequence either way, so the access has to be focused.
                    if self.arrays.contains_key(&*v.val.to_string()) {
                        let f = self.focus_elem(inner, None)?;
                        let t = self.fresh("elem");
                        self.lines
                            .push(format!("let {} = {}_read {};", t, f.pn, f.at));
                        self.lines.extend(f.close_read);
                        return Ok(t);
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
            ExprT::Member(..) | ExprT::Index(..) => {
                let hint = match &e.val {
                    ExprT::Member(_, f) => f.val.to_string(),
                    _ => "elem".to_string(),
                };
                let f = self.place(e)?;
                let t = self.fresh(&hint);
                self.lines
                    .push(format!("let {} = {}_read {};", t, f.pn, f.at));
                self.lines.extend(f.close_read);
                Ok(t)
            }
            ExprT::BoolLit(b) => Ok(if *b { "true" } else { "false" }.to_string()),
            ExprT::IntLit(n, ty) => int_literal(self.tds, n, ty),
            ExprT::Cast(inner, to) => {
                let from = self.ty_of(inner)?;
                // A literal cast to another integer type is that literal at
                // that type. C has already reduced it, and going through
                // `convert` would emit a cast that cannot always be justified
                // -- `(size_t) 0` is a signed-to-unsigned conversion whose
                // obligation nothing discharges.
                if let ExprT::IntLit(n, _) = &strip_vattr(inner).val {
                    if **n >= BigInt::ZERO {
                        if let Ok(l) = int_literal(self.tds, n, to) {
                            return Ok(l);
                        }
                    }
                }
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
            ExprT::UnOp(UnOp::Neg, inner) => {
                // C negates modulo 2^width at unsigned type; at signed type it
                // is the same overflow obligation as subtraction.
                let ty = self.ty_of(e)?;
                let a = self.rvalue(inner)?;
                match &self.tds.resolve(&ty).val {
                    TypeT::Int {
                        signed: false,
                        width,
                    } => Ok(format!(
                        "(0{} `Pulse.Lib.C.UInt{}.sub_wrap` {})",
                        int_suffix(false, *width)?,
                        width,
                        a
                    )),
                    TypeT::Int {
                        signed: true,
                        width,
                    } if self.signed_ok => Ok(format!(
                        "(0{} `FStar.Int{}.sub` {})",
                        int_suffix(true, *width)?,
                        width,
                        a
                    )),
                    TypeT::Int { signed: true, .. } => Err(
                        "signed arithmetic, whose overflow obligation needs the untranslated `_requires`"
                            .to_string(),
                    ),
                    _ => Err(format!("a negation of {}", describe(&ty))),
                }
            }
            ExprT::UnOp(UnOp::BitNot, inner) => {
                let ty = self.ty_of(e)?;
                let a = self.rvalue(inner)?;
                match &self.tds.resolve(&ty).val {
                    TypeT::Int {
                        signed: false,
                        width,
                    } => Ok(format!("(FStar.UInt{}.lognot {})", width, a)),
                    _ => Err(format!("a bitwise complement of {}", describe(&ty))),
                }
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
        // Only scalars have machine operations, so only scalars can have a
        // stack slot. A struct local needs a `struct_S_stack_alloc`, which the
        // generated struct layer does not provide: its points-to is the
        // conjunction of its fields' and says nothing about the storage as a
        // whole.
        if !has_repr(self.tds, ty) {
            return Err(format!(
                "local `{}` is {}",
                name.val,
                describe(self.tds.resolve(ty))
            ));
        }
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
        if let ExprT::Deref(inner) = &lhs.val {
            if let ExprT::Var(v) = &inner.val {
                if self.arrays.contains_key(&*v.val.to_string()) {
                    let f = self.focus_elem(inner, None)?;
                    self.lines
                        .push(format!("{}_write {} {};", f.pn, f.at, value));
                    self.lines.extend(f.close_write);
                    return Ok(());
                }
            }
        }
        if matches!(lhs.val, ExprT::Member(..) | ExprT::Index(..)) {
            let f = self.place(lhs)?;
            self.lines
                .push(format!("{}_write {} {};", f.pn, f.at, value));
            self.lines.extend(f.close_write);
            return Ok(());
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
            StmtT::Assert(e) => {
                let p = self.prop(e)?;
                self.lines.push(format!("assert (pure {});", p));
                Ok(())
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

    /// Translate a statement sequence that runs to the end of the function:
    /// it either falls off the end or returns, and either way it is
    /// responsible for releasing every slot the function allocated. A
    /// `return` inside an `if` is what makes this recursive rather than a
    /// loop -- the statements after such an `if` are the arm the `return` did
    /// not take, so they become the other branch.
    fn rest(&mut self, stmts: &[Rc<Stmt>]) -> Result<Option<String>, String> {
        for (i, s) in stmts.iter().enumerate() {
            match &s.val {
                StmtT::Return(e) => {
                    let v = match e {
                        Some(e) => Some(self.rvalue(e)?),
                        None => None,
                    };
                    self.release_from(0);
                    return Ok(v);
                }
                StmtT::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } if returns(then_branch) || returns(else_branch) => {
                    let cty = self.ty_of(cond)?;
                    if !matches!(self.tds.resolve(&cty).val, TypeT::Bool) {
                        return Err("an `if` on a non-boolean condition".to_string());
                    }
                    let c = self.rvalue(cond)?;
                    // Whatever follows the `if` is only reached on the paths
                    // that did not return, so it belongs to the arm that falls
                    // through. Appending it to that arm is what turns an early
                    // `return` into an expression.
                    let after = &stmts[i + 1..];
                    let mut then_stmts: Vec<Rc<Stmt>> = then_branch.to_vec();
                    let mut else_stmts: Vec<Rc<Stmt>> = else_branch.to_vec();
                    if !returns(then_branch) {
                        then_stmts.extend(after.iter().cloned());
                    }
                    if !returns(else_branch) {
                        else_stmts.extend(after.iter().cloned());
                    }
                    let (then_lines, then_val) = self.tail_arm(&then_stmts)?;
                    let (else_lines, else_val) = self.tail_arm(&else_stmts)?;
                    if then_val.is_some() != else_val.is_some() {
                        return Err("an `if` where only one arm returns a value".to_string());
                    }
                    self.lines.push(format!("if ({})", c));
                    self.lines.push("{".to_string());
                    self.lines.extend(then_lines.iter().map(|l| indent(l)));
                    if let Some(v) = then_val {
                        self.lines.push(indent(&v));
                    }
                    self.lines.push("} else {".to_string());
                    self.lines.extend(else_lines.iter().map(|l| indent(l)));
                    if let Some(v) = else_val {
                        self.lines.push(indent(&v));
                    }
                    self.lines.push("}".to_string());
                    return Ok(None);
                }
                _ => {
                    self.env.push_stmt(s);
                    self.stmt(s)?;
                }
            }
        }
        self.release_from(0);
        Ok(None)
    }

    /// One arm of a returning `if`, translated into its own line buffer
    /// against a copy of the state at the `if`.
    fn tail_arm(&mut self, stmts: &[Rc<Stmt>]) -> Result<(Vec<String>, Option<String>), String> {
        let outer_env = self.env.clone();
        let outer_lines = std::mem::take(&mut self.lines);
        let outer_out = self.out_params.clone();
        let outer_slots = self.slots.clone();
        let outer_in_branch = std::mem::replace(&mut self.in_branch, true);

        let out = self
            .rest(stmts)
            .map(|v| (std::mem::take(&mut self.lines), v));

        self.in_branch = outer_in_branch;
        self.slots = outer_slots;
        self.out_params = outer_out;
        self.env = outer_env;
        self.lines = outer_lines;
        out
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
        let outer_in_branch = std::mem::replace(&mut self.in_branch, true);

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

        self.in_branch = outer_in_branch;
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
        // `size_t` is eight unsigned bytes, but F* keeps it a separate type
        // with its own casts rather than an `Int` of a known width.
        (
            TypeT::Int {
                signed: false,
                width,
            },
            TypeT::SizeT,
        ) if *width != 8 => Ok(format!("(sizet_of_uint{} {})", width, v)),
        (
            TypeT::SizeT,
            TypeT::Int {
                signed: false,
                width,
            },
        ) if *width == 32 || *width == 64 => {
            Ok(format!("(FStar.SizeT.sizet_to_uint{} {})", width, v))
        }
        (
            TypeT::SizeT,
            TypeT::Int {
                signed: false,
                width,
            },
        ) => Ok(format!(
            "(FStar.Int.Cast.uint64_to_uint{} (FStar.SizeT.sizet_to_uint64 {}))",
            width, v
        )),
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
        // `ptr` is abstract and so has no decidable equality of its own; the
        // model provides one, which is what C's `==` on pointers means.
        TypeT::Pointer(..) | TypeT::FnPtr { .. } => {
            return match op {
                BinOp::Eq => Ok("`ptr_eq`".to_string()),
                _ => Err("an operator on a pointer".to_string()),
            };
        }
        _ => return Err(format!("an operator on {}", describe(t))),
    };
    match op {
        BinOp::Eq => return Ok("=".to_string()),
        BinOp::Lt => return Ok(format!("`{}.lt`", m)),
        BinOp::LEq => return Ok(format!("`{}.lte`", m)),
        // The bitwise operators are defined on the whole range at both
        // signednesses, so they need no obligation and no wrapping variant.
        // `FStar.SizeT` does not have them, hence the guard.
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor if matches!(t.val, TypeT::Int { .. }) => {
            return Ok(format!(
                "`FStar.{}.log{}`",
                m,
                match op {
                    BinOp::BitAnd => "and",
                    BinOp::BitOr => "or",
                    _ => "xor",
                }
            ));
        }
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

/// A place opened for one access: where it is, what type it is, and the lines
/// that put it back after a read or after a write.
struct Focus {
    at: String,
    pn: String,
    close_read: Vec<String>,
    close_write: Vec<String>,
}

/// Peel the virtual attributes `elab` wraps around an expression.
fn strip_vattr(e: &Expr) -> &Expr {
    match &e.val {
        ExprT::VAttr(_, inner) => strip_vattr(inner),
        _ => e,
    }
}

fn expr_kind_of(e: &ExprT) -> &'static str {
    match e {
        ExprT::Member(..) => "a struct field",
        ExprT::Index(..) => "an array element",
        ExprT::Deref(..) => "another dereference",
        _ => "a computed pointer",
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
    // goes through `array_focus` rather than a plain read. Record what each one
    // needs to be focused: the element's Palow type and its size.
    let mut arrays = HashMap::new();
    for a in &defn.decl.args {
        if extent(tds, &a.ty) != Some(Extent::Array) {
            continue;
        }
        let (Some(name), Some(pt)) = (a.name.as_ref(), pointee(tds, &a.ty)) else {
            continue;
        };
        let (Some(pn), Some(esize)) = (palow_name(tds, pt), palow_sizeof(tds, pt)) else {
            continue;
        };
        if !has_repr(tds, pt) {
            continue;
        }
        arrays.insert(
            name.val.to_string(),
            ArrayParam {
                pn,
                esize: format!("{}sz", esize),
            },
        );
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
        in_branch: false,
        arrays,
        requires_ok: sig.contract && !defn.decl.requires.is_empty(),
        params: defn
            .decl
            .args
            .iter()
            .filter_map(|a| a.name.as_ref().map(|n| n.val.to_string()))
            .collect(),
    };

    let tail = b.rest(&defn.body)?;
    if let Some(t) = tail {
        b.lines.push(t);
    }
    Ok(b.lines)
}

/// Whether a C block always leaves the function. Only the shape the
/// translation needs: a trailing `return`.
fn returns(stmts: &Stmts) -> bool {
    matches!(stmts.last().map(|s| &s.val), Some(StmtT::Return(_)))
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
