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
    /// Its size in bytes, which together with the offset is what says where
    /// the padding is.
    size: u64,
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

    /// How many bytes of the object the field occupies.
    fn size(&self, tds: &Typedefs, ty: &Type) -> Option<u64> {
        match self {
            FieldShape::One { .. } => palow_sizeof(tds, ty),
            FieldShape::Array { esize, len, .. } => Some(esize * len),
        }
    }

    /// The write-only view of the field's storage. An array has no such view
    /// in the model, which is what keeps a struct with an array field out of
    /// automatic storage for now.
    fn uninit(&self, at: &str) -> Option<String> {
        match self {
            FieldShape::One { pn } => Some(format!("{}_pts_to_uninit {}", pn, at)),
            FieldShape::Array { .. } => None,
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
    /// `_pure` functions that were successfully emitted as F* definitions, and
    /// so may appear in a specification and in a body without being sequenced.
    pure_fns: HashSet<String>,
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
            pure_fns: HashSet::new(),
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

/// A type with typedefs *and* the annotation wrappers stripped.
///
/// `resolve` only follows typedefs, which is what the points-to layer wants: a
/// `_plain int32_t *` and an `int32_t *` have the same predicate but are not
/// the same C declaration. An *operator*, though, is chosen by the underlying
/// scalar type alone, and `_plain` says nothing about it.
fn peel<'b>(tds: &'b Typedefs, ty: &'b Type) -> &'b Type {
    let mut ty = tds.resolve(ty);
    for _ in 0..64 {
        ty = match &ty.val {
            TypeT::Refine(t, _)
            | TypeT::RefineAlways(t, _)
            | TypeT::RefineUninit(t, _)
            | TypeT::RefineValue(t, ..)
            | TypeT::Plain(t)
            | TypeT::Nullable(t) => tds.resolve(t),
            _ => return ty,
        };
    }
    ty
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
        // A specification integer is unbounded, which is what `_let` needs to
        // state a range condition without first having to prove it.
        TypeT::SpecInt => Some("int".to_string()),
        TypeT::SpecNat => Some("nat".to_string()),
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
///
/// `_plain` is not one of them. It is exactly the annotation that says the
/// parameter is a bare address and the function owns nothing behind it, which
/// is what lets a caller pass `NULL`. `_nullable` is not one either: what it
/// owns is `unless_null p (...)`, which is not translated yet, and pretending
/// it were an unconditional points-to would be a contract no caller could
/// satisfy.
fn pointee<'a>(tds: &'a Typedefs, ty: &'a Type) -> Option<&'a Rc<Type>> {
    match &tds.resolve(ty).val {
        TypeT::Pointer(to, _) => Some(to),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..) => pointee(tds, t),
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
    /// The ownership the contract grants over what the parameters point to.
    /// A function body never has to restate this -- Pulse carries it -- except
    /// at a loop, whose invariant Pulse cannot invent.
    owned: Vec<OwnedParam>,
    /// Whether the C function's own `_requires`/`_ensures` made it into the
    /// specification. When they did not, the contract we emit is weaker than
    /// the source says, and in particular cannot discharge an overflow
    /// obligation -- see `Body::signed_ok`.
    contract: bool,
}

/// One parameter's pointee ownership, in the form a loop invariant needs: the
/// C name of the parameter, the F* type of the value, and the points-to less
/// its final value argument.
struct OwnedParam {
    base: String,
    vty: String,
    /// `array_pts_to uint32_t_repr 4 var_a 1.0R ` -- append a value to it.
    pre: String,
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
    /// C locals that the specification may mention, mapped to the term
    /// standing for their current value. A function contract has none -- a
    /// local is not in scope at the boundary -- but a loop invariant does:
    /// every live slot is bound existentially and named here.
    locals: HashMap<String, String>,
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
            // `_live(x)` says the storage exists. A loop invariant restates the
            // whole ownership frame anyway, so by the time this is read the
            // claim has already been made and there is nothing left to say.
            ExprT::Live(_) => Ok("True".to_string()),
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
                    let (a, b) = (self.prop(l, w)?, self.prop(r, w)?);
                    // `_live(x) && p` is just `p` once the frame carries the
                    // storage, and a loop invariant is mostly `_live` clauses.
                    if matches!(op, BinOp::LogAnd) {
                        if a == "True" {
                            return Ok(b);
                        }
                        if b == "True" {
                            return Ok(a);
                        }
                    }
                    return Ok(format!("({} {} {})", a, o, b));
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
        // Signed arithmetic is undefined on overflow, so where a contract
        // measures it the source can only mean the mathematical result, and
        // the two agree on every program C defines. Saying it that way rather
        // than as `Int32.v (a `Int32.add` b)` also avoids a term whose own
        // typing needs the `_requires` -- which Pulse does not have in scope
        // when it types the `ensures`. Unsigned arithmetic wraps and is
        // defined, so it must keep its operator.
        if let ExprT::BinOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), l, r) = &strip_vattr(e).val
        {
            if matches!(self.tds.resolve(&ty).val, TypeT::Int { signed: true, .. }) {
                return Ok(format!(
                    "({} {} {})",
                    self.num(l, w)?,
                    op.to_str(),
                    self.num(r, w)?
                ));
            }
        }
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
                        // A literal cast to a scalar type is that literal at
                        // that type. C has already reduced it, so no
                        // conversion is being described -- this is how `a[0]`
                        // elaborates, and how `true` and `false` reach here.
                        if let ExprT::IntLit(n, _) = &strip_vattr(inner).val {
                            if let Ok(l) = int_literal(self.tds, n, to) {
                                return Ok(l);
                            }
                        }
                        // C's conversions to and from `_Bool`, which is how
                        // a predicate written over integers reaches a `bool`
                        // and back. Neither can lose information, so neither
                        // raises an obligation.
                        if matches!(to.val, TypeT::Bool) {
                            if let Some(m) = self.int_module(&from) {
                                return Ok(format!("({}.v {} <> 0)", m, self.value(inner, w)?));
                            }
                        }
                        if matches!(self.tds.resolve(&from).val, TypeT::Bool) {
                            if let (Ok(one), Ok(zero)) = (
                                int_literal(self.tds, &BigInt::from(1), to),
                                int_literal(self.tds, &BigInt::ZERO, to),
                            ) {
                                return Ok(format!(
                                    "(if {} then {} else {})",
                                    self.value(inner, w)?,
                                    one,
                                    zero
                                ));
                            }
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
                if let Some(l) = self.locals.get(&*v.val.to_string()) {
                    Ok(l.clone())
                } else if &*v.val == "return" {
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
                if let (UnOp::Neg, ExprT::IntLit(n, _)) = (op, &strip_vattr(inner).val) {
                    // `-1000` is a literal, not a negation of one: C has no
                    // negative literals, so this is the only way one is
                    // written.
                    if let Ok(l) = int_literal(self.tds, &-(**n).clone(), ty) {
                        return Ok(l);
                    }
                }
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
                // A `_Bool`-valued expression in *value* position -- the body
                // of a `_let`, say -- has to come out as an F* `bool`, not as a
                // proposition, because something is going to compare it with
                // `true`.
                if let Some(o) = match op {
                    BinOp::LogAnd => Some("&&"),
                    BinOp::LogOr => Some("||"),
                    _ => None,
                } {
                    return Ok(format!(
                        "({} {} {})",
                        self.value(l, w)?,
                        o,
                        self.value(r, w)?
                    ));
                }
                let ty = self.ty_of(l)?;
                if matches!(self.tds.resolve(&ty).val, TypeT::SpecInt | TypeT::SpecNat)
                    && let Some(o) = match op {
                        BinOp::Eq => Some("="),
                        BinOp::Lt => Some("<"),
                        BinOp::LEq => Some("<="),
                        _ => None,
                    }
                {
                    return Ok(format!(
                        "({} {} {})",
                        self.value(l, w)?,
                        o,
                        self.value(r, w)?
                    ));
                }
                if !matches!(self.tds.resolve(&ty).val, TypeT::SpecInt | TypeT::SpecNat) {
                    // Machine arithmetic in a specification means what it means
                    // in a body: unsigned wraps, and signed is undefined unless
                    // something rules the overflow out. The same operator table
                    // serves both, so a contract cannot quietly describe an
                    // operation the body would not perform.
                    let o = binop(self.tds, *op, &ty, false)?;
                    return Ok(format!(
                        "({} {} {})",
                        self.value(l, w)?,
                        o,
                        self.value(r, w)?
                    ));
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
            ExprT::Cond(c, t, f) => Ok(format!(
                "(if {} then {} else {})",
                self.value(c, w)?,
                self.value(t, w)?,
                self.value(f, w)?
            )),
            ExprT::FnCall(name, args) if self.tds.pure_fns.contains(&*name.val.to_string()) => {
                let mut out = format!("func_{}", name.val);
                for a in args.iter() {
                    out += &format!(" {}", self.value(a, w)?);
                }
                if args.is_empty() {
                    out += " ()";
                }
                Ok(format!("({})", out))
            }
            _ => Err(format!("{} in a contract", expr_kind(e))),
        }
    }
}

/// Build the F* definition for one `_let`, or explain why we cannot.
///
/// A `_let` exists only at specification level: it is a name for a
/// proposition or a mathematical value that several contracts share. There is
/// no code for it and no memory involved, so nothing about it depends on the
/// memory model -- it is the same definition Palow would want under any model.
fn emit_let_decl(tds: &Typedefs, env: &Env, ld: &LetDecl) -> Result<String, String> {
    if ld.is_impure {
        return Err("it is impure".to_string());
    }
    if ld.is_rec {
        return Err("it is recursive".to_string());
    }
    if matches!(tds.resolve(&ld.ret_type).val, TypeT::SLProp) {
        return Err("it defines an slprop".to_string());
    }
    let mut params: Vec<String> = Vec::new();
    for (i, arg) in ld.params.iter().enumerate() {
        let pname = match &arg.name {
            Some(n) => format!("var_{}", n.val),
            None => format!("arg_{}", i),
        };
        let fty = fstar_type(tds, &arg.ty)
            .ok_or_else(|| format!("parameter {} is {}", pname, describe(tds.resolve(&arg.ty))))?;
        params.push(format!("({}: {})", pname, fty));
    }
    if params.is_empty() {
        params.push("()".to_string());
    }
    let ret = fstar_type(tds, &ld.ret_type)
        .ok_or_else(|| format!("it returns {}", describe(tds.resolve(&ld.ret_type))))?;

    let sp = Spec {
        tds,
        env,
        pointees: HashMap::new(),
        arrays: HashSet::new(),
        guards: RefCell::new(Vec::new()),
        ret: "ret".to_string(),
        locals: HashMap::new(),
    };
    let clause = |es: &Exprs| -> Result<String, String> {
        let mut props: Vec<String> = Vec::new();
        for e in es.iter() {
            sp.guards.borrow_mut().clear();
            let p = sp.prop(e, When::Pre)?;
            if !sp.guards.borrow().is_empty() {
                return Err("a contract with a side condition".to_string());
            }
            props.push(p);
        }
        Ok(if props.is_empty() {
            "True".to_string()
        } else {
            props.join(r" /\ ")
        })
    };
    let req = clause(&ld.requires)?;
    let ens = clause(&ld.ensures)?;
    let body = sp.value(&ld.body, When::Pre)?;

    // `GTot` rather than `Tot`: a `_let` is only ever used in a specification,
    // and keeping it ghost means nothing can accidentally extract it.
    let ty = if req == "True" && ens == "True" {
        format!("GTot {}", ret)
    } else {
        format!(
            "Ghost {} (requires ({})) (ensures (fun {} -> {}))",
            ret, req, sp.ret, ens
        )
    };
    Ok(format!(
        "let func_{} {} : {} =\n  {}\n\n",
        ld.name.val,
        params.join(" "),
        ty,
        body
    ))
}

/// Build the F* definition for one `_pure` C function, or explain why we
/// cannot.
///
/// A `_pure` function has no side effects and no memory of its own, so its
/// body is an expression rather than a sequence of statements. That is what
/// makes it usable in a specification: `_assert(f(x) == 1)` is a proposition
/// about a term, and the term is this definition, unfolded by the SMT solver
/// like any other.
fn emit_pure_fn(
    tds: &Typedefs,
    env: &Env,
    decl: &FnDecl,
    body: Option<&[Rc<Stmt>]>,
) -> Result<String, String> {
    // A ghost argument needs an erased implicit, which is not translated yet.
    if decl.is_rec && decl.decreases.is_none() {
        return Err("it is recursive without a `_decreases`".to_string());
    }
    if !decl.ghost_args.is_empty() {
        return Err("it takes a ghost argument".to_string());
    }
    let mut params: Vec<String> = Vec::new();
    for (i, arg) in decl.args.iter().enumerate() {
        let pname = match &arg.name {
            Some(n) => format!("var_{}", n.val),
            None => format!("arg_{}", i),
        };
        let fty = fstar_type(tds, &arg.ty)
            .ok_or_else(|| format!("parameter {} is {}", pname, describe(tds.resolve(&arg.ty))))?;
        params.push(format!("({}: {})", pname, fty));
    }
    if params.is_empty() {
        params.push("()".to_string());
    }
    let ret = fstar_type(tds, &decl.ret_type).unwrap_or_else(|| "unit".to_string());

    let mut sp = Spec {
        tds,
        env,
        pointees: HashMap::new(),
        arrays: HashSet::new(),
        guards: RefCell::new(Vec::new()),
        ret: "ret".to_string(),
        locals: HashMap::new(),
    };
    let clause = |sp: &Spec, es: &Exprs| -> Result<String, String> {
        let mut props: Vec<String> = Vec::new();
        for e in es.iter() {
            sp.guards.borrow_mut().clear();
            let p = sp.prop(e, When::Pre)?;
            if !sp.guards.borrow().is_empty() {
                return Err("a contract with a side condition".to_string());
            }
            props.push(p);
        }
        Ok(if props.is_empty() {
            "True".to_string()
        } else {
            props.join(r" /\ ")
        })
    };
    let req = clause(&sp, &decl.requires)?;
    let ens = clause(&sp, &decl.ensures)?;

    let dec = match &decl.decreases {
        Some(d) => {
            sp.guards.borrow_mut().clear();
            Some(sp.num(d, When::Pre)?)
        }
        None => None,
    };

    let value = match body {
        Some(b) => Some(pure_body(&mut sp, b)?),
        None => None,
    };
    let ty = if req == "True" && ens == "True" && dec.is_none() {
        ret
    } else {
        let mut t = format!(
            "Pure {} (requires ({})) (ensures (fun {} -> {}))",
            ret, req, sp.ret, ens
        );
        if let Some(d) = dec {
            t += &format!(" (decreases ({}))", d);
        }
        t
    };
    // A `_pure` function that is only declared here -- `pal_c_assert_enabled`
    // in `pal.h` is the one that matters -- still has to be a term, or an
    // `_assert` that mentions it could not be translated. Assuming it is
    // exactly as safe as the existing translator's treatment: the contract is
    // all a caller may rely on either way.
    let Some(value) = value else {
        return Ok(format!(
            "assume val func_{} {} : {}\n\n",
            decl.name.val,
            params.join(" "),
            ty
        ));
    };
    Ok(format!(
        "let {}func_{} {} : {} =\n  {}\n\n",
        if decl.is_rec { "rec " } else { "" },
        decl.name.val,
        params.join(" "),
        ty,
        value
    ))
}

/// The body of a `_pure` function, as a single F* term.
///
/// Statements after an `if` belong to both of its arms, exactly as in the
/// existing translator: C's control flow joins, and an expression's does not,
/// so the continuation is duplicated instead.
fn pure_body(sp: &mut Spec, stmts: &[Rc<Stmt>]) -> Result<String, String> {
    let Some(first) = stmts.first() else {
        return Err("a pure function that falls off the end".to_string());
    };
    let rest = &stmts[1..];
    match &first.val {
        StmtT::Return(Some(e)) => sp.value(e, When::Pre),
        StmtT::Return(None) => Ok("()".to_string()),
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            let c = sp.value(cond, When::Pre)?;
            let mut t: Vec<Rc<Stmt>> = then_branch.to_vec();
            t.extend_from_slice(rest);
            let mut f: Vec<Rc<Stmt>> = else_branch.to_vec();
            f.extend_from_slice(rest);
            let a = pure_body(sp, &t)?;
            let b = pure_body(sp, &f)?;
            Ok(format!("(if {} then {} else {})", c, a, b))
        }
        StmtT::Let(name, _, init) => {
            let v = sp.value(init, When::Pre)?;
            pure_let(sp, name, v, rest)
        }
        // `T x; x = e;` is the same thing spelled in two statements. Only that
        // shape is accepted: a local assigned twice is not a `let`, and a
        // local read before it is assigned has no value at all.
        StmtT::Decl(name, _) => {
            let Some(next) = rest.first() else {
                return Err("a pure local that is never assigned".to_string());
            };
            let StmtT::Assign(lhs, rhs) = &next.val else {
                return Err("a pure local that is not assigned immediately".to_string());
            };
            match &strip_vattr(lhs).val {
                ExprT::Var(v) if v.val == name.val => {}
                _ => return Err("a pure local that is not assigned immediately".to_string()),
            }
            let value = sp.value(rhs, When::Pre)?;
            pure_let(sp, name, value, &rest[1..])
        }
        _ => Err(format!("{} in a pure function", stmt_kind(first))),
    }
}

/// Bind one local and translate what follows under the binding.
fn pure_let(
    sp: &mut Spec,
    name: &Ident,
    value: String,
    rest: &[Rc<Stmt>],
) -> Result<String, String> {
    let n = format!("var_{}", name.val);
    let shadowed = sp.locals.insert(name.val.to_string(), n.clone());
    let body = pure_body(sp, rest);
    match shadowed {
        Some(old) => sp.locals.insert(name.val.to_string(), old),
        None => sp.locals.remove(&*name.val.to_string()),
    };
    Ok(format!("(let {} = {} in {})", n, value, body?))
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
    let mut owned: Vec<OwnedParam> = Vec::new();
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
                owned.push(OwnedParam {
                    base: base.clone(),
                    vty: vty.clone(),
                    pre: pts_to(&perm, ""),
                });
                let v = format!("(reveal {})", vname);
                pointees.insert(base, (Some(v.clone()), Some(v)));
            }
            ParamMode::Consumed => {
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                req.push(pts_to("1.0R", &vname));
                owned.push(OwnedParam {
                    base: base.clone(),
                    vty: vty.clone(),
                    pre: pts_to("1.0R", ""),
                });
                pointees.insert(base, (Some(format!("(reveal {})", vname)), None));
            }
            ParamMode::Regular => {
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                req.push(pts_to("1.0R", &vname));
                owned.push(OwnedParam {
                    base: base.clone(),
                    vty: vty.clone(),
                    pre: pts_to("1.0R", ""),
                });
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
        locals: HashMap::new(),
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
        owned,
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
            let Some(fsize) = shape.size(tds, &fty) else {
                ok = false;
                bad = format!("field `{}` has no size", fname);
                break;
            };
            fields.push(StructField {
                name: fname,
                ty: fty,
                offset: off,
                size: fsize,
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

    // The bytes of the object that belong to no field. C says they are part
    // of the object, so ownership of the struct has to include them: otherwise
    // a struct that came out of automatic storage could never go back into it,
    // having lost the gaps on the way through `_pts_to`. They carry no value,
    // so they are existentially quantified and only their length is pinned.
    let mut gaps: Vec<(u64, u64)> = Vec::new();
    let mut sorted: Vec<&StructField> = si.fields.iter().collect();
    sorted.sort_by_key(|f| f.offset);
    let mut cursor = 0u64;
    for f in &sorted {
        if f.offset > cursor {
            gaps.push((cursor, f.offset - cursor));
        }
        cursor = cursor.max(f.offset + f.size);
    }
    if si.size > cursor {
        gaps.push((cursor, si.size - cursor));
    }
    c += &format!(
        "let {}_padding (a: ptr) (p: perm) : slprop =\n  {}\n\n",
        sn,
        if gaps.is_empty() {
            "emp".to_string()
        } else {
            gaps.iter()
                .map(|(off, len)| {
                    format!(
                        "(exists* g. mem_pts_to {} p g ** pure (len g == {}))",
                        if *off == 0 {
                            "a".to_string()
                        } else {
                            format!("(a +! {}sz)", off)
                        },
                        len
                    )
                })
                .collect::<Vec<_>>()
                .join(" **\n  ")
        }
    );

    c += &format!(
        "let {}_pts_to ([@@@mkey] a: ptr) (p: perm) (x: {}) : slprop =\n  {} **\n  {}_padding a p\n\n",
        sn,
        sn,
        conj("x", None),
        sn
    );

    for f in &si.fields {
        let fty = field_type(tds, &f.ty).unwrap();
        let at = format!("(a +! {}_offsetof_{})", sn, f.name);
        let upd = format!("({{ x with fld_{} = y }})", f.name);
        let owned = |v: &str| f.shape.pts_to(&at, v);
        c += &format!(
            "let {}_hole_{} (a: ptr) (p: perm) (x: {}) : slprop =\n  {} **\n  {}_padding a p\n\n",
            sn,
            f.name,
            sn,
            conj("x", Some(&f.name)),
            sn
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
    c += &emit_struct_storage(tds, name, &gaps);
    c
}

/// The automatic-storage operations for one struct: allocate, initialise,
/// forget and free. There is no axiom here for the struct; there is a proof,
/// carving `mem_stack_alloc`'s flat byte range into the fields and the gaps
/// with the same `mem_split` the scalar layer uses.
///
/// The carve goes right to left. `mem_split a n` leaves the prefix at `a` and
/// the suffix at `a +! n`, so splitting at descending offsets keeps every
/// suffix pointer literally `a +! <absolute offset>`. Splitting the other way
/// round nests the arithmetic -- `((a +! 4) +! 4) +! 1` -- and the solver does
/// not see through it.
fn emit_struct_storage(tds: &Typedefs, name: &str, gaps: &[(u64, u64)]) -> String {
    let si = &tds.structs[name];
    let sn = format!("struct_{}", name);
    // A field with no write-only view keeps the whole struct out of automatic
    // storage: there would be no way to hand back what was never claimed.
    let mut uninit = Vec::new();
    for f in &si.fields {
        // A nested struct field would need its own `_claim_uninit`, which the
        // generated layer does not have yet: the carve stops at the scalars.
        let u = if has_repr(tds, &f.ty) {
            f.shape
                .uninit(&format!("(a +! {}_offsetof_{})", sn, f.name))
        } else {
            None
        };
        let Some(u) = u else {
            return format!(
                "(* struct {}: no automatic storage, field `{}` has no uninitialised view *)\n\n",
                name, f.name
            );
        };
        uninit.push(u);
    }

    // `a +! 0sz` is `a` only up to `add_zero`, and a `rewrite` will use that
    // lemma but slprop matching will not. Writing the first field's address as
    // plain `a` keeps the two in step.
    let at = |off: u64| {
        if off == 0 {
            "a".to_string()
        } else {
            format!("(a +! {}sz)", off)
        }
    };

    let mut c = String::new();
    c += &format!(
        "let {}_pts_to_uninit (a: ptr) : slprop =\n  {} **\n  {}_padding a 1.0R\n\n",
        sn,
        uninit.join(" **\n  "),
        sn
    );

    // Every boundary inside the object, in the order the splits have to run.
    let mut bounds: Vec<u64> = si
        .fields
        .iter()
        .map(|f| f.offset)
        .chain(gaps.iter().map(|(off, _)| *off))
        .filter(|off| *off != 0)
        .collect();
    bounds.sort_unstable();
    bounds.dedup();

    let mut alloc = String::new();
    for off in bounds.iter().rev() {
        alloc += &format!("  mem_split a {}sz;\n", off);
    }
    for f in &si.fields {
        let FieldShape::One { pn } = &f.shape else {
            unreachable!()
        };
        alloc += &format!("  {}_claim_uninit {};\n", pn, at(f.offset));
        alloc += &format!(
            "  rewrite ({pn}_pts_to_uninit {off})\n    as ({pn}_pts_to_uninit (a +! {sn}_offsetof_{f}));\n",
            pn = pn,
            off = at(f.offset),
            sn = sn,
            f = f.name
        );
    }
    c += &format!(
        "fn {sn}_stack_alloc ()\n\
         \x20 returns a : ptr\n\
         \x20 ensures {sn}_pts_to_uninit a\n\
         {{\n\
         \x20 let a = mem_stack_alloc {sn}_sizeof;\n\
         {alloc}\
         \x20 fold {sn}_padding a 1.0R;\n\
         \x20 fold {sn}_pts_to_uninit a;\n\
         \x20 a\n}}\n\n",
        sn = sn,
        alloc = alloc
    );

    // Freeing runs the carve backwards. `mem_join a n` needs the two halves
    // adjacent, so the joins go left to right, which is the reverse of the
    // order the splits ran in.
    let mut free = String::new();
    free += &format!("  unfold {}_pts_to_uninit a;\n", sn);
    free += &format!("  unfold {}_padding a 1.0R;\n", sn);
    for f in &si.fields {
        let FieldShape::One { pn } = &f.shape else {
            unreachable!()
        };
        free += &format!(
            "  rewrite ({pn}_pts_to_uninit (a +! {sn}_offsetof_{f}))\n    as ({pn}_pts_to_uninit {off});\n",
            pn = pn,
            sn = sn,
            f = f.name,
            off = at(f.offset)
        );
        free += &format!("  {}_reveal_uninit {};\n", pn, at(f.offset));
    }
    for off in bounds.iter() {
        free += &format!("  mem_join a {}sz;\n", off);
    }
    c += &format!(
        "fn {sn}_stack_free (a: ptr)\n\
         \x20 requires {sn}_pts_to_uninit a\n\
         {{\n{free}  mem_stack_free a;\n}}\n\n",
        sn = sn,
        free = free
    );

    // Going from a live struct back to storage is per field: the padding is
    // already in both predicates and passes straight through.
    let mut forget = String::new();
    forget += &format!("  unfold {}_pts_to a 1.0R x;\n", sn);
    for f in &si.fields {
        let FieldShape::One { pn } = &f.shape else {
            unreachable!()
        };
        forget += &format!("  {}_forget (a +! {}_offsetof_{});\n", pn, sn, f.name);
    }
    c += &format!(
        "ghost fn {sn}_forget (a: ptr) (#x: {sn})\n\
         \x20 requires {sn}_pts_to a 1.0R x\n\
         \x20 ensures  {sn}_pts_to_uninit a\n\
         {{\n{forget}  fold {sn}_pts_to_uninit a;\n}}\n\n",
        sn = sn,
        forget = forget
    );

    let mut write = String::new();
    write += &format!("  unfold {}_pts_to_uninit a;\n", sn);
    for f in &si.fields {
        let FieldShape::One { pn } = &f.shape else {
            unreachable!()
        };
        write += &format!(
            "  {}_write_uninit (a +! {}_offsetof_{}) x.fld_{};\n",
            pn, sn, f.name, f.name
        );
    }
    c += &format!(
        "fn {sn}_write_uninit (a: ptr) (x: {sn})\n\
         \x20 requires {sn}_pts_to_uninit a\n\
         \x20 ensures  {sn}_pts_to a 1.0R x\n\
         {{\n{write}  fold {sn}_pts_to a 1.0R x;\n}}\n\n",
        sn = sn,
        write = write
    );
    c
}

/// Whether a struct has the generated automatic-storage operations, which is
/// the same condition `emit_struct_storage` checks: every field needs an
/// uninitialised view, and an array field has none.
fn storable_struct(tds: &Typedefs, ty: &Type) -> bool {
    let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(tds, ty).val else {
        return false;
    };
    match tds.structs.get(&*n.val) {
        Some(si) => si
            .fields
            .iter()
            .all(|f| matches!(f.shape, FieldShape::One { .. }) && has_repr(tds, &f.ty)),
        None => false,
    }
}

/// A global's initialiser, as a closed F* term. Only literals qualify: a
/// global whose value has to be computed has an initialiser the emitter would
/// have to evaluate, and C's constant expressions are not the subset this pass
/// covers.
fn const_expr(tds: &Typedefs, ty: &Type, e: &Expr) -> Option<String> {
    // `_Bool b = true;` reaches the IR as a cast of `1`, so the target type
    // decides how the literal reads, not the literal itself.
    if matches!(tds.resolve(ty).val, TypeT::Bool) {
        return match &strip_vattr(e).val {
            ExprT::BoolLit(b) => Some(if *b { "true" } else { "false" }.to_string()),
            ExprT::IntLit(n, _) => {
                Some(if **n == BigInt::ZERO { "false" } else { "true" }.to_string())
            }
            ExprT::Cast(inner, _) => const_expr(tds, ty, inner),
            _ => None,
        };
    }
    match &strip_vattr(e).val {
        ExprT::IntLit(n, _) => int_literal(tds, n, ty).ok(),
        // A negative initialiser is a negation of a literal, not a negative
        // literal; folding it here keeps `int_literal`'s signedness check.
        ExprT::UnOp(UnOp::Neg, inner) => match &strip_vattr(inner).val {
            ExprT::IntLit(n, _) => int_literal(tds, &-(**n).clone(), ty).ok(),
            _ => None,
        },
        ExprT::Cast(inner, _) => const_expr(tds, ty, inner),
        _ => None,
    }
}

/// The globals of a translation unit.
///
/// Palow does not change the design PAL already settled on here, because that
/// design is about *who owns a global*, and the answer does not depend on how
/// memory is modelled. An immutable global -- `const`, or annotated `_pure` --
/// has a value that is fixed for the life of the program, so it is published
/// as an F* constant and read with no ownership at all; the permission that
/// would let something write through its address stays under an existential in
/// `acquire`, so no client can ever obtain a full one. A mutable global gets
/// its address and nothing else: with no points-to ever produced for it, no
/// permission to read or write through the address can be derived, so handing
/// the address out is inert, and reads of the global itself are refused.
///
/// The addresses are assumed rather than allocated. C gives a global a single
/// fixed address for the whole run, which is exactly a constant of type `ptr`,
/// and pointer identity between two mentions of `&g` then holds definitionally.
fn emit_globals(tds: &Typedefs, tu: &TranslationUnit) -> String {
    let mut out = String::new();
    for decl in &tu.decls {
        let gv = match &decl.val {
            DeclT::GlobalVar(g) => g,
            _ => continue,
        };
        if gv.is_enum_constant || global_var_is_array(gv) {
            continue;
        }
        let name = &gv.name.val;
        // The address is a `ptr` whatever the global's type is, so it is
        // published for every addressable global; only the value and the
        // permission that goes with it need a type the model covers.
        let typed = palow_name(tds, &gv.ty)
            .filter(|_| has_repr(tds, &gv.ty))
            .and_then(|pn| fstar_type(tds, &gv.ty).map(|fty| (pn, fty)));
        // The value is known only for an immutable global that this file
        // initialises. `extern const T g;` is immutable but its value lives in
        // another translation unit; a tentative `const T g;` is zero, but
        // spelling that out per type is the aggregate work milestone 5 left.
        let value = if gv.is_pure && !gv.is_extern {
            gv.init.as_ref().and_then(|e| const_expr(tds, &gv.ty, e))
        } else {
            None
        };
        out += &format!(
            "assume val addr_var_{} : ptr
",
            name
        );
        out += &format!(
            "assume val addr_var_{}_not_null : squash (not (is_null addr_var_{}))
",
            name, name
        );
        if let (Some(v), Some((pn, fty))) = (value, typed) {
            out += &format!(
                "let var_{} : {} = {}
",
                name, fty, v
            );
            // The permission is existentially quantified, so a client can read
            // through the address but can never gather a full one and write.
            out += &format!(
                "assume val acquire_var_{} : unit -> stt_ghost unit emp_inames emp\n  (fun _ -> exists* (p: perm). {}_pts_to addr_var_{} p var_{})\n",
                name, pn, name, name
            );
        }
        out += "
";
    }
    if out.is_empty() {
        String::new()
    } else {
        format!(
            "(* Globals. An immutable global is an F* constant plus an address; a\n   mutable one is an address and nothing else, which is inert because no\n   permission for it can ever be derived. *)\n\n{}",
            out
        )
    }
}

/// One function's place in the output: its generated text, and which other
/// functions in this file that text names.
struct FnItem<'a> {
    name: String,
    code: String,
    uses: HashSet<String>,
    defn: Option<&'a FnDefn>,
    env: Env,
    sig: Option<FnSurface>,
}

/// The order to write the functions out in, callees first.
///
/// C only needs a declaration before a call; F* needs the definition, and
/// everything Palow emits lands in one module. Returning the back edges rather
/// than an order lets the caller re-translate just the bodies that close a
/// cycle.
fn toposort(items: &[FnItem]) -> Result<Vec<usize>, Vec<(String, String)>> {
    let index: HashMap<&str, usize> = items
        .iter()
        .enumerate()
        .map(|(i, it)| (it.name.as_str(), i))
        .collect();
    let mut state = vec![0u8; items.len()];
    let mut order = Vec::new();
    let mut back = Vec::new();
    // An explicit stack: a deep call chain is not the place to run out of
    // native stack. `(node, next child)`.
    let mut stack: Vec<(usize, usize)> = Vec::new();
    for start in 0..items.len() {
        if state[start] != 0 {
            continue;
        }
        state[start] = 1;
        stack.push((start, 0));
        while let Some((n, k)) = stack.pop() {
            // The neighbours are taken in a fixed order so the output does not
            // depend on the hash set's iteration order.
            let mut kids: Vec<&str> = items[n].uses.iter().map(|s| s.as_str()).collect();
            kids.sort_unstable();
            if k < kids.len() {
                stack.push((n, k + 1));
                let Some(&m) = index.get(kids[k]) else {
                    continue;
                };
                match state[m] {
                    0 => {
                        state[m] = 1;
                        stack.push((m, 0));
                    }
                    1 => back.push((items[n].name.clone(), items[m].name.clone())),
                    _ => {}
                }
            } else {
                state[n] = 2;
                order.push(n);
            }
        }
    }
    if back.is_empty() {
        Ok(order)
    } else {
        Err(back)
    }
}

pub fn emit_palow(tu: &TranslationUnit) -> Vec<PalowModule> {
    let mut tds = Typedefs::new(tu);
    let structs = collect_structs(tu, &mut tds);
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
    code += "open Pulse.Lib.C.Palow.Nullable\n";
    code += "open Pulse.Lib.C.Palow.Alloc\n";
    code += "module Seq = FStar.Seq\n\n";
    for m in ["Int8", "Int16", "Int32", "Int64"] {
        code += &format!("module {} = FStar.{}\n", m, m);
    }
    for m in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        code += &format!("module {} = FStar.{}\n", m, m);
    }
    code += "module SizeT = FStar.SizeT\n\n";
    code += &structs;
    code += &emit_globals(&tds, tu);

    // `_let` definitions first: they are the vocabulary the `_pure` functions
    // and the contracts are written in.
    for decl in &tu.decls {
        let DeclT::LetDecl(ld) = &decl.val else {
            continue;
        };
        let mut env = base.clone();
        for a in &ld.params {
            env.push_arg(a, crate::env::LocalDeclKind::RValue);
        }
        tds.pure_fns.insert(ld.name.val.to_string());
        match emit_let_decl(&tds, &env, ld) {
            Ok(t) => code += &t,
            Err(why) => {
                tds.pure_fns.remove(&*ld.name.val.to_string());
                code += &format!(
                    "(* `{}` is not an F* definition: {} *)\n\n",
                    ld.name.val, why
                );
            }
        }
    }

    // `_pure` functions first, and as F* definitions rather than Pulse `fn`s.
    // A `_pure` function is the vocabulary a contract is written in, so it has
    // to be a term an `_ensures` or an `_assert` can mention; a `fn` is a
    // computation, and Pulse rejects one in a specification because its
    // postcondition carries no `rewrites_to`.
    let defined: HashSet<String> = tu
        .decls
        .iter()
        .filter_map(|d| match &d.val {
            DeclT::FnDefn(d) => Some(d.decl.name.val.to_string()),
            _ => None,
        })
        .collect();
    for decl in &tu.decls {
        let (fndecl, body) = match &decl.val {
            DeclT::FnDefn(d) => (&d.decl, Some(&*d.body)),
            // A declaration whose definition is elsewhere in this file is
            // handled when the definition is reached.
            DeclT::FnDecl(d) if !defined.contains(&*d.name.val.to_string()) => (d, None),
            _ => continue,
        };
        if !fndecl.is_pure {
            continue;
        }
        let mut env = base.clone();
        env.push_fn_decl_args_for_body(fndecl);
        // Inserted first so that a recursive body can name itself; taken back
        // out again if the definition does not come out.
        tds.pure_fns.insert(fndecl.name.val.to_string());
        match emit_pure_fn(&tds, &env, fndecl, body) {
            Ok(t) => {
                code += &t;
            }
            // Falling back to the Pulse `fn` keeps the function callable from
            // code even when it cannot be a term. Only a specification that
            // mentions it is lost.
            Err(why) => {
                tds.pure_fns.remove(&*fndecl.name.val.to_string());
                code += &format!(
                    "(* `{}` is not an F* definition: {} *)\n\n",
                    fndecl.name.val, why
                );
            }
        }
    }
    let tds = tds;

    // The whole callee map is built before any body is translated. What a call
    // may do depends only on the callee's *signature*, so nothing here needs
    // the callees' code -- and building it up front is what lets a body call a
    // function defined further down the file, which C allows and F* does not.
    let mut callees: HashMap<String, Callee> = HashMap::new();
    let mut items: Vec<FnItem> = Vec::new();
    for decl in &tu.decls {
        let (fndecl, defn) = match &decl.val {
            DeclT::FnDefn(d) => (&d.decl, Some(d)),
            DeclT::FnDecl(d) => (d, None),
            _ => continue,
        };
        if tds.pure_fns.contains(&*fndecl.name.val.to_string()) {
            continue;
        }
        let mut env = base.clone();
        env.push_fn_decl_args_for_body(fndecl);
        let sig = match emit_fn(&tds, &env, fndecl) {
            Ok(s) => s,
            Err(why) => {
                items.push(FnItem {
                    name: fndecl.name.val.to_string(),
                    code: format!("(* skipped {}: {} *)\n\n", fndecl.name.val, why),
                    uses: HashSet::new(),
                    defn: None,
                    env,
                    sig: None,
                });
                continue;
            }
        };

        // A call may only pass ownership it can name: a value, or a pointer to
        // an object the caller holds and gets back unchanged. `_out` and
        // `_consumes` parameters move ownership across the call, which the
        // caller's slot bookkeeping does not model yet.
        callees.insert(
            fndecl.name.val.to_string(),
            Callee {
                simple: if !fndecl
                    .args
                    .iter()
                    .all(|a| matches!(a.mode, ParamMode::Regular | ParamMode::Const))
                {
                    Err("moves ownership across the call")
                } else if !fndecl.ghost_args.is_empty() {
                    Err("takes a ghost argument")
                } else if fndecl.args.iter().any(|a| refined(&tds, &a.ty)) {
                    // A `_refine` on a parameter is part of the contract on
                    // both sides of the call, and is not translated yet; a
                    // caller that could not see it would be proving against a
                    // specification weaker than the source's.
                    Err("takes a `_refine`d argument")
                } else {
                    Ok(())
                },
                void: matches!(tds.resolve(&fndecl.ret_type).val, TypeT::Void),
                contract: sig.contract,
            },
        );
        items.push(FnItem {
            name: fndecl.name.val.to_string(),
            code: String::new(),
            uses: HashSet::new(),
            defn,
            env,
            sig: Some(sig),
        });
    }

    // Recursion has to be broken somewhere: F* would need `let rec`/`rec fn`
    // and a termination argument that C does not supply, so a call on a cycle
    // is refused and the rest of the body is kept. `forbidden` grows until the
    // call graph is acyclic, which it must reach because each round removes at
    // least one edge.
    let mut forbidden: HashMap<String, HashSet<String>> = HashMap::new();
    let order = loop {
        for it in &mut items {
            let Some(sig) = &it.sig else { continue };
            let empty = HashSet::new();
            let no = forbidden.get(&it.name).unwrap_or(&empty);
            let body = match it.defn {
                None => Err("it has no definition here".to_string()),
                Some(d) => emit_body(&tds, it.env.clone(), d, sig, &callees, no),
            };
            it.uses = match &body {
                Ok(b) => b.uses.clone(),
                Err(_) => HashSet::new(),
            };
            let mut out = String::new();
            match &body {
                Ok(b) if b.divergent => out += "divergent\n",
                _ => {}
            }
            out += &sig.decl;
            match body {
                Ok(TranslatedBody { lines, .. }) => {
                    out += "{\n";
                    for l in &lines {
                        out += &format!("  {}\n", l);
                    }
                    out += "}\n\n";
                }
                Err(why) => {
                    out += &format!("{{\n  admit() (* body: {} *)\n}}\n\n", why);
                }
            }
            it.code = out;
        }
        match toposort(&items) {
            Ok(o) => break o,
            Err(back) => {
                for (from, to) in back {
                    forbidden.entry(from).or_default().insert(to);
                }
            }
        }
    };
    for i in order {
        code += &items[i].code;
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
    /// The F* type of the value the slot holds. A loop invariant has to bind
    /// one existential per live slot, and the binder needs a type.
    fstar_ty: String,
    init: bool,
}

/// One open field focus: where the field is, and how to close it again.
struct FieldFocus {
    /// The Palow name of the struct the field belongs to.
    sn: String,
    /// The address of the struct.
    a: String,
    /// The address of the field.
    at: String,
    close_read: Vec<String>,
    close_write: Vec<String>,
}

/// A block of heap storage held in a local pointer.
///
/// `malloc` may fail, so between the allocation and the null test the block is
/// under `unless_null` and nothing at all can be done with it. Once the source
/// tests the pointer, the non-null arm eliminates the guard and claims the
/// bytes at the pointee's type, and from there the block behaves exactly like
/// a stack slot -- with a `freeable` alongside it, which is what `free` spends.
#[derive(Clone)]
struct Block {
    /// The C local holding the pointer.
    var: String,
    /// The name the allocation was bound to. The local is not reassigned while
    /// the block is tracked, so this names the same pointer the local holds,
    /// and using it directly avoids a load whose result the frame would then
    /// have to be re-stated in terms of.
    tmp: String,
    /// The pointee's Palow type name.
    pn: String,
    /// The byte pattern the allocator promises: `uninit` for `malloc`,
    /// `zeroed` for `calloc`. The zeroing is not carried into the claim yet, so
    /// a `calloc`ed block still arrives write-only; the shape only has to match
    /// what the allocator's postcondition said.
    fill: &'static str,
    /// Whether the null test has been passed. Until it has, the block is under
    /// `unless_null` and unusable.
    checked: bool,
    /// Whether the pointee has been written. `malloc` hands back uninitialised
    /// storage, so the first store through the pointer is an initialising one.
    init: bool,
    /// Whether `free` has already taken the block back.
    freed: bool,
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
    /// Why a call to this function cannot be emitted, if it cannot. A call may
    /// only pass ownership it can name: a value, or a pointer to an object the
    /// caller holds and gets back unchanged.
    simple: Result<(), &'static str>,
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
    /// Functions this body must not call, because doing so would close a cycle
    /// in the call graph.
    forbidden: &'a HashSet<String>,
    uses: HashSet<String>,
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
    /// Whether the expression being translated is a loop guard rather than a
    /// specification. A guard is real code, so a call may stay in it.
    in_guard: bool,
    /// Array-kind pointer parameters, by C name.
    arrays: HashMap<String, ArrayParam>,
    /// The function's parameters, by C name. Ownership of what a pointer points
    /// to is granted by the contract, and the contract only names parameters.
    params: HashSet<String>,
    /// Whether the function has a translated `_requires`. Bounds and overflow
    /// obligations are discharged by it, so without one there is nothing to
    /// discharge them with.
    requires_ok: bool,
    /// The ownership the contract grants over the parameters' pointees, which
    /// a loop invariant has to restate.
    owned: &'a [OwnedParam],
    /// Whether any parameter is `_out`. Such a parameter's storage is
    /// uninitialised on entry and initialised by the body, so it is not a
    /// fixed part of the frame a loop invariant can restate.
    has_out: bool,
    /// Set by a loop: the function has to be declared `divergent`, since PAL
    /// translates no `decreases` measure.
    divergent: bool,
    /// Heap blocks held in locals, in allocation order.
    blocks: Vec<Block>,
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

    /// Whether a global has a value published as an F* constant: it is
    /// immutable, this file initialises it, and the initialiser is a literal.
    fn global_value(&self, v: &Ident) -> bool {
        match self.env.lookup_global_var(v) {
            Some(gv) => {
                !gv.is_enum_constant
                    && !global_var_is_array(gv)
                    && gv.is_pure
                    && !gv.is_extern
                    && has_repr(self.tds, &gv.ty)
                    && gv
                        .init
                        .as_ref()
                        .is_some_and(|e| const_expr(self.tds, &gv.ty, e).is_some())
            }
            None => false,
        }
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
                    // A global has an address, but nothing here owns the
                    // storage behind it, so an access *through* that address
                    // has nothing to prove itself with. `&g` on its own is
                    // fine, and goes through `global_addr` instead.
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
                    fstar_ty: fstar_type(self.tds, &ty)
                        .ok_or_else(|| format!("`{}` has no F* type", v.val))?,
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
                // A checked block's pointee is owned just like a parameter's,
                // and naming the allocation directly rather than loading the
                // local keeps the frame stated in terms of the same pointer.
                ExprT::Var(v)
                    if self
                        .blocks
                        .iter()
                        .any(|b| b.var == *v.val && b.checked && !b.freed) =>
                {
                    let b = self
                        .blocks
                        .iter()
                        .find(|b| b.var == *v.val && b.checked && !b.freed)
                        .unwrap();
                    Ok(b.tmp.clone())
                }
                ExprT::Var(v) if self.params.contains(&*v.val.to_string()) => self.rvalue(inner),
                // `malloc` may fail, so an allocation the source never tested
                // is genuinely not owned. This is a real difference from the
                // old model, whose allocator could not return null.
                ExprT::Var(v) if self.blocks.iter().any(|b| b.var == *v.val && !b.freed) => {
                    Err(format!(
                        "a dereference of `{}`, whose allocation was not checked for null",
                        v.val
                    ))
                }
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
            other => Err(format!(
                "{}, which is not an lvalue Palow can address",
                expr_kind_of(other)
            )),
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
                let pn = self.field_pn(base, f)?;
                let ff = self.focus_field(base, f)?;
                let mut close_read = vec![format!("{}_unfocus_read_{} {};", ff.sn, f.val, ff.a)];
                close_read.extend(ff.close_read);
                let mut close_write = vec![format!("{}_unfocus_{} {};", ff.sn, f.val, ff.a)];
                close_write.extend(ff.close_write);
                Ok(Focus {
                    pn,
                    at: ff.at,
                    close_read,
                    close_write,
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

    /// Emit the focus of one field. Returns the struct's Palow name, the base
    /// address, the field's address, and the lines that close whatever had to
    /// be opened to reach the base -- in read and in write form, because a
    /// write through an inner field changes the outer struct's value and a
    /// read does not.
    fn focus_field(&mut self, base: &Expr, f: &Ident) -> Result<FieldFocus, String> {
        let (sn, _) = self.struct_of(base)?;
        let (a, close_read, close_write) = self.base_addr(base)?;
        let at = format!("({} +! {}_offsetof_{})", a, sn, f.val);
        self.lines.push(format!("{}_focus_{} {};", sn, f.val, a));
        Ok(FieldFocus {
            sn,
            a,
            at,
            close_read,
            close_write,
        })
    }

    /// The address of the object a field belongs to. Usually just `addr`, but
    /// a field of a *nested* struct -- which is what an anonymous member and a
    /// first-field cast both come out as -- has to focus the outer field first,
    /// and that focus stays open until the access through it is done.
    fn base_addr(&mut self, base: &Expr) -> Result<(String, Vec<String>, Vec<String>), String> {
        if let ExprT::Member(b2, f2) = &strip_vattr(base).val {
            let fty = self.field_ty(b2, f2)?;
            if matches!(
                &peel(self.tds, &fty).val,
                TypeT::TypeRef(TypeRefKind::Struct(_))
            ) {
                let inner = self.focus_field(b2, f2)?;
                let mut close_read =
                    vec![format!("{}_unfocus_read_{} {};", inner.sn, f2.val, inner.a)];
                close_read.extend(inner.close_read);
                let mut close_write = vec![format!("{}_unfocus_{} {};", inner.sn, f2.val, inner.a)];
                close_write.extend(inner.close_write);
                return Ok((inner.at, close_read, close_write));
            }
        }
        Ok((self.addr(base)?, Vec::new(), Vec::new()))
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
                let ff = self.focus_field(base, f)?;
                // Even a read through an array field goes back with the
                // general unfocus: what comes out of the element access is a
                // sequence, and `Seq.upd xs i (Seq.index xs i)` is only `xs`
                // up to a lemma that is not worth generating per field.
                let mut close = vec![format!("{}_unfocus_{} {};", ff.sn, f.val, ff.a)];
                close.extend(ff.close_write);
                Ok((ff.at, pn, format!("{}sz", esize), close))
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
    /// An operand of a specification, with its loads left in place.
    ///
    /// Pulse A-normalises calls appearing in an `assert (pure ...)` or in a
    /// `while` head, so the loads an operand needs do not have to be lifted to
    /// `let`s first. Leaving them in place is what makes the resulting
    /// obligation mention the contract's or the invariant's own ghost binder
    /// instead of a generated temporary.
    ///
    /// The decision is made from the lines the access actually emitted rather
    /// than from the shape of the expression: if all of them are simple
    /// bindings they are substituted back and dropped, and if any of them is
    /// not -- a focus has to be opened and closed around its load, and two of
    /// those in one operand could not be nested -- the names stay.
    ///
    /// Only a *read* may be substituted back. A read's postcondition says
    /// `rewrites_to`, which is exactly what lets Pulse use it in a
    /// specification; an ordinary call has no such postcondition, and putting
    /// one in an `assert` is refused with "cannot find rewrites_to in post".
    ///
    /// Nor may the call be lifted out and the name used instead. An `_assert`
    /// is a specification: it does not run, and it must not make the program
    /// do anything it would not otherwise do. A C function may have side
    /// effects, so hoisting `_assert(f(x) > 0)` into `let t = f x; assert (t >
    /// 0)` changes the meaning of the program. Such an assertion is refused.
    /// Only a `_pure` function, which is emitted as an F* definition rather
    /// than as a computation, can be mentioned in one.
    ///
    /// A loop guard is the other way round. It is real code -- `while (f(i))`
    /// calls `f` on every iteration, so lifting the call out would run it
    /// once -- and Pulse accepts a computation in the head of a `while`. So a
    /// guard keeps the call where the source put it, and nothing is refused.
    fn inline(&mut self, e: &Expr) -> Result<String, String> {
        let before = self.lines.len();
        let mut v = self.rvalue(e)?;
        let added: Vec<String> = self.lines[before..].to_vec();
        let mut bound = Vec::new();
        for l in &added {
            let Some(rest) = l.strip_prefix("let ").and_then(|r| r.strip_suffix(';')) else {
                return Ok(v);
            };
            let Some((n, d)) = rest.split_once(" = ") else {
                return Ok(v);
            };
            let inlinable = self.in_guard
                || d.split_whitespace()
                    .next()
                    .is_some_and(|h| h.ends_with("_read"));
            bound.push((n.to_string(), format!("({})", d), inlinable));
        }
        for i in (0..bound.len()).rev() {
            if !bound[i].2 {
                continue;
            }
            let (n, d) = (bound[i].0.clone(), bound[i].1.clone());
            v = v.replace(&n, &d);
            for j in 0..bound.len() {
                if j != i {
                    bound[j].1 = bound[j].1.replace(&n, &d);
                }
            }
        }
        self.lines.truncate(before);
        if let Some((_, d, _)) = bound.iter().find(|(_, _, i)| !*i) {
            return Err(format!(
                "a call to `{}`, which a specification cannot make",
                d.trim_matches(['(', ')'])
                    .split_whitespace()
                    .next()
                    .unwrap_or(d)
                    .trim_start_matches("func_")
            ));
        }
        Ok(v)
    }

    /// A specification proposition in *statement* position, as in `_assert`.
    ///
    /// A contract has ghost binders for everything it owns, so it can name a
    /// pointee without touching memory. Inside a body there are no such
    /// binders -- the translator deliberately tracks no values -- so each
    /// mention of an object becomes a real load. That is sound and loses
    /// nothing: a read is the identity on the state, and `rewrites_to` in its
    /// postcondition makes the loaded name definitionally the stored value, so
    /// the assertion Pulse checks is the one the C source wrote. Pulse hoists
    /// the loads out of the `assert` itself, so most of them need no name --
    /// see `read`.
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
                    Ok(format!("({} == true)", self.inline(e)?))
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
            // Mathematical integers are F*'s own, so arithmetic over them is
            // the same arithmetic with no overflow obligation attached.
            match &strip_vattr(e).val {
                ExprT::IntLit(n, _) => return Ok(format!("({})", n)),
                ExprT::UnOp(UnOp::Neg, inner) => {
                    let v = self.num(inner)?;
                    return Ok(format!("(- {})", v));
                }
                ExprT::BinOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), l, r) => {
                    let a = self.num(l)?;
                    let b = self.num(r)?;
                    return Ok(format!("({} {} {})", a, op.to_str(), b));
                }
                _ => {}
            }
            return Err("a specification computation in an assertion".to_string());
        }
        // `(_specint) b` on a `_Bool` is C's integer promotion, which is what
        // makes `_assert(my_true == 1)` mean what the source says.
        if matches!(self.tds.resolve(&ty).val, TypeT::Bool) {
            return Ok(format!("(if {} then 1 else 0)", self.inline(e)?));
        }
        match int_module(self.tds, &ty) {
            Some(m) => Ok(format!("({}.v {})", m, self.inline(e)?)),
            None => self.inline(e),
        }
    }

    fn rvalue(&mut self, e: &Expr) -> Result<String, String> {
        match &e.val {
            ExprT::VAttr(_, inner) => self.rvalue(inner),
            // A struct literal is an F* record literal. C fills any field the
            // initialiser leaves out with zero, and the emitter has no zero to
            // write for an arbitrary field type, so a partial initialiser is
            // refused rather than guessed at.
            ExprT::StructInit(sname, inits) => {
                let Some(si) = self.tds.structs.get(&*sname.val) else {
                    return Err(format!("an initialiser for struct {}", sname.val));
                };
                let order: Vec<String> = si.fields.iter().map(|f| f.name.clone()).collect();
                if order.len() != inits.len() {
                    return Err(format!(
                        "a partial initialiser for struct {}, which leaves fields at zero",
                        sname.val
                    ));
                }
                let mut vals = Vec::new();
                for fname in &order {
                    let Some((_, fe)) = inits.iter().find(|(n, _)| *n.val == **fname) else {
                        return Err(format!(
                            "an initialiser for struct {} that does not name `{}`",
                            sname.val, fname
                        ));
                    };
                    vals.push((fname.clone(), self.rvalue(fe)?));
                }
                Ok(format!(
                    "({{ {} }})",
                    vals.iter()
                        .map(|(n, v)| format!("fld_{} = {}", n, v))
                        .collect::<Vec<_>>()
                        .join("; ")
                ))
            }
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
                } else if self.global_value(v) {
                    // An immutable global is a constant, and reading it needs
                    // no ownership at all -- which is the whole point of
                    // publishing it as one.
                    Ok(format!("var_{}", v.val))
                } else if self.env.lookup_global_var(v).is_some() {
                    Err(format!(
                        "a read of `{}`, a global whose value is not fixed here",
                        v.val
                    ))
                } else {
                    Err(format!("`{}` is not in scope", v.val))
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
                // `peel`, not `resolve`: a `_plain int32_t *` is a pointer as
                // far as a conversion is concerned, and the annotation
                // wrappers would otherwise hide that.
                convert(peel(self.tds, &from), peel(self.tds, to), &v)
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
            ExprT::Ref(inner) => match &strip_vattr(inner).val {
                // A global's address is a constant of type `ptr`, so it needs
                // no slot -- and two mentions of `&g` are the same pointer
                // definitionally, which is what C says. Nothing can be done
                // with it without ownership, which is what makes handing it
                // out inert.
                ExprT::Var(v)
                    if self.env.lookup_var(v).is_none()
                        && self.env.addressable_global(v).is_some() =>
                {
                    Ok(format!("addr_var_{}", v.val))
                }
                _ => self.addr(inner),
            },
            ExprT::FnCall(name, args) if self.tds.pure_fns.contains(&*name.val.to_string()) => {
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
            .ok_or_else(|| format!("`{}` is not declared in this file", name.val))?;
        if self.forbidden.contains(&*name.val.to_string()) {
            return Err(format!("`{}`, which is recursive", name.val));
        }
        self.uses.insert(name.val.to_string());
        if let Err(why) = c.simple {
            return Err(format!("`{}` {}", name.val, why));
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
        // A slot needs the four automatic-storage operations. Scalars get them
        // from the machine layer; a struct gets them generated, provided every
        // field has an uninitialised view to carve out of the raw bytes.
        if !has_repr(self.tds, ty) && !storable_struct(self.tds, ty) {
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
            fstar_ty: fstar_type(self.tds, ty)
                .ok_or_else(|| format!("local `{}` has no F* type", name.val))?,
            init: false,
        });
        Ok(pn)
    }

    /// The `unless_null` payload of an allocation: the block's bytes and the
    /// right to give them back. It has to be written out in full because the
    /// elimination is by `rewrite`, which cannot see through the `if` inside
    /// `unless_null` on its own.
    fn block_slprop(b: &Block) -> String {
        format!(
            "(mem_pts_to {t} 1.0R ({f} (SizeT.v {pn}_sizeof)) ** freeable {t} {pn}_sizeof)",
            t = b.tmp,
            f = b.fill,
            pn = b.pn
        )
    }

    /// An allocation of a single object, with the Palow name of the type
    /// allocated. `malloc(sizeof(T) * n)` is an array allocation and is not
    /// this; nor is a flexible-array-member allocation.
    fn alloc_of(&self, e: &Expr) -> Option<(&'static str, String)> {
        let e = strip_vattr(e);
        let e = match &e.val {
            ExprT::Cast(inner, _) => strip_vattr(inner),
            _ => e,
        };
        match &e.val {
            ExprT::Malloc(ty) => palow_name(self.tds, ty).map(|pn| ("malloc", pn)),
            ExprT::Calloc(ty) => palow_name(self.tds, ty).map(|pn| ("calloc", pn)),
            _ => None,
        }
    }

    /// `p = malloc(sizeof(T))` for a local pointer `p`.
    ///
    /// The pointer itself is an ordinary value and goes into `p`'s slot like
    /// any other. What is new is the resource that comes with it, which stays
    /// under `unless_null` until the source tests the pointer.
    fn allocate(&mut self, var: &Ident, which: &str, pn: &str) -> Result<String, String> {
        if self.in_branch {
            return Err("an allocation inside a branch".to_string());
        }
        let tmp = self.fresh(&var.val);
        self.lines
            .push(format!("let {} = {} {}_sizeof;", tmp, which, pn));
        self.blocks.retain(|b| b.var != *var.val);
        self.blocks.push(Block {
            var: var.val.to_string(),
            tmp: tmp.clone(),
            pn: pn.to_string(),
            fill: if which == "calloc" {
                "zeroed"
            } else {
                "uninit"
            },
            checked: false,
            init: false,
            freed: false,
        });
        Ok(tmp)
    }

    /// A test of a tracked block's pointer against null, as an index into
    /// `blocks` and whether it is the *then* arm that runs when the pointer is
    /// null.
    fn null_test(&self, cond: &Expr) -> Option<(usize, bool)> {
        // `p != NULL` reaches the IR as `!(p == 0)`; there is no `Ne`.
        // `if (p)` reaches the IR as `if ((_Bool) p)`, which carries no
        // information the test does not.
        fn peel(e: &Expr) -> Rc<Expr> {
            match &strip_vattr(e).val {
                ExprT::Cast(inner, _) => peel(inner),
                _ => Rc::new(strip_vattr(e).clone()),
            }
        }
        let (cond, mut null_when_true) = match &peel(cond).val {
            ExprT::UnOp(UnOp::Not, inner) => (peel(inner), false),
            _ => (peel(cond), true),
        };
        let (a, b) = match &strip_vattr(&cond).val {
            ExprT::BinOp(BinOp::Eq, a, b) => (a.clone(), b.clone()),
            // `if (p)` is a bare truth test on the pointer.
            ExprT::Var(_) => {
                null_when_true = !null_when_true;
                let i = self
                    .blocks
                    .iter()
                    .position(|blk| match &strip_vattr(&cond).val {
                        ExprT::Var(v) => blk.var == *v.val,
                        _ => false,
                    })?;
                return if self.blocks[i].checked {
                    None
                } else {
                    Some((i, null_when_true))
                };
            }
            _ => return None,
        };
        let is_zero =
            |e: &Expr| matches!(&strip_vattr(e).val, ExprT::IntLit(n, _) if **n == BigInt::ZERO);
        let var = if is_zero(&b) {
            strip_vattr(&a)
        } else if is_zero(&a) {
            strip_vattr(&b)
        } else {
            return None;
        };
        let name = match &var.val {
            ExprT::Var(v) => v.val.to_string(),
            _ => return None,
        };
        let i = self.blocks.iter().position(|blk| blk.var == name)?;
        if self.blocks[i].checked {
            return None;
        }
        Some((i, null_when_true))
    }

    /// The emitted condition of a null test, in the polarity the C source
    /// wrote it, so that the arms stay where the source put them.
    fn null_cond(tmp: &str, null_when_true: bool) -> String {
        if null_when_true {
            format!("is_null {}", tmp)
        } else {
            format!("not (is_null {})", tmp)
        }
    }

    /// The lines that open each arm of a null test. The arm that runs when the
    /// pointer is non-null eliminates the guard and claims the bytes at the
    /// pointee's type, which is exactly the state a stack allocation would
    /// have left; the other arm discards the guard, which is `emp` there.
    fn null_test_arms(&self, i: usize) -> (Vec<String>, Vec<String>) {
        let b = &self.blocks[i];
        let sl = Self::block_slprop(b);
        (
            vec![format!("elim_unless_null_null {} {};", b.tmp, sl)],
            vec![
                format!("elim_unless_null {} {};", b.tmp, sl),
                format!("{}_claim_uninit {};", b.pn, b.tmp),
            ],
        )
    }

    /// `free(p)`.
    ///
    /// The block goes back the way it came: forget whatever the pointee last
    /// held, spend the write-only view for the bytes it stands for, and hand
    /// those and the `freeable` to `free`. Requiring the whole block back at
    /// full permission is what makes freeing a subrange, or a pointer into the
    /// middle of a block, unprovable.
    fn free(&mut self, arg: &Expr) -> Result<(), String> {
        let name = match &strip_vattr(arg).val {
            ExprT::Var(v) => v.val.to_string(),
            _ => return Err("a `free` of something other than a local".to_string()),
        };
        let i = self
            .blocks
            .iter()
            .position(|b| b.var == name && b.checked && !b.freed)
            .ok_or_else(|| {
                format!(
                    "a `free` of `{}`, which does not hold a checked block",
                    name
                )
            })?;
        let (tmp, pn, init) = {
            let b = &self.blocks[i];
            (b.tmp.clone(), b.pn.clone(), b.init)
        };
        if init {
            self.lines.push(format!("{}_forget {};", pn, tmp));
        }
        self.lines.push(format!("{}_reveal_uninit {};", pn, tmp));
        self.lines.push(format!("free {};", tmp));
        self.blocks[i].freed = true;
        Ok(())
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
            if let ExprT::Var(v) = &strip_vattr(inner).val {
                if let Some(i) = self
                    .blocks
                    .iter()
                    .position(|b| b.var == *v.val && b.checked && !b.freed)
                {
                    let op = if self.blocks[i].init {
                        "write"
                    } else {
                        "write_uninit"
                    };
                    self.blocks[i].init = true;
                    let tmp = self.blocks[i].tmp.clone();
                    self.lines.push(format!("{}_{} {} {};", pn, op, tmp, value));
                    return Ok(());
                }
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

    /// A `while` loop.
    ///
    /// This is the one place where the model asks the source for something the
    /// old one did not. Pulse computes the join for an `if` by itself, but no
    /// system invents a loop invariant, so the invariant has to name the whole
    /// ownership frame: one existential per live local and per parameter
    /// pointee, the points-to that binds each, and only then the proposition
    /// the C source wrote. `_live(x)` in the source therefore carries no
    /// information any more -- the frame already claims the storage -- and the
    /// C invariant is read purely as a proposition over those binders.
    ///
    /// Nothing has to relate the loop's boolean to those binders: Pulse re-runs
    /// the condition against the invariant and hands its truth to the body and
    /// its falsity to the exit. The condition is therefore translated once, as
    /// a computation, with its loads left in the `while` head so that
    /// `rewrites_to` states them in terms of the invariant's own binders.
    ///
    /// A loop makes the function divergent. PAL does not translate a
    /// `decreases` measure, and C gives it nothing to derive one from.
    /// The ownership frame at a control-flow join, as `exists*` binders, the
    /// points-to conjuncts over them, and whatever the source's own clause
    /// says about their values.
    ///
    /// A loop invariant and the join of a `switch` need exactly the same
    /// thing: nothing here tracks values, so every live slot has to be bound
    /// existentially and the annotation written in terms of those binders.
    fn frame(
        &self,
        clause: &Exprs,
        what: &str,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), String> {
        let mut binders: Vec<String> = Vec::new();
        let mut owns: Vec<String> = Vec::new();
        let mut locals: HashMap<String, String> = HashMap::new();
        for s in &self.slots {
            if !s.init {
                // The frame would have to say that the slot still holds
                // storage rather than a value, and the body would have to
                // leave it that way. C that writes a local for the first time
                // inside a loop is real, but it is not this milestone.
                return Err(format!("{} with `{}` not yet written", what, s.name));
            }
            let b = format!("inv_{}", s.name);
            binders.push(format!("({}: {})", b, s.fstar_ty));
            owns.push(format!("{}_pts_to loc_{} 1.0R {}", s.palow_ty, s.name, b));
            locals.insert(s.name.clone(), b);
        }
        let mut pointees: HashMap<String, (Option<String>, Option<String>)> = HashMap::new();
        for o in self.owned {
            let b = format!("inv_val_{}", o.base);
            binders.push(format!("({}: {})", b, o.vty));
            owns.push(format!("{}{}", o.pre, b));
            pointees.insert(o.base.clone(), (Some(b.clone()), Some(b)));
        }

        let spec = Spec {
            tds: self.tds,
            env: &self.env,
            pointees,
            arrays: self.arrays.keys().cloned().collect(),
            guards: RefCell::new(Vec::new()),
            ret: String::new(),
            locals,
        };
        let mut props: Vec<String> = Vec::new();
        for e in clause.iter() {
            spec.guards.borrow_mut().clear();
            let p = spec.prop(e, When::Pre)?;
            let guards = spec.guards.borrow();
            // `_live` clauses translate to `True`: the frame has already
            // claimed the storage. Dropping them keeps the invariant readable.
            if p == "True" && guards.is_empty() {
                continue;
            }
            props.push(if guards.is_empty() {
                p
            } else {
                format!(r"({} /\ {})", guards.join(r" /\ "), p)
            });
        }
        Ok((binders, owns, props))
    }

    /// The same frame, written out as one slprop.
    fn frame_slprop(&self, clause: &Exprs, what: &str, indent: &str) -> Result<String, String> {
        let (binders, owns, props) = self.frame(clause, what)?;
        let sep = format!("\n{}", indent);
        let quant = if binders.is_empty() {
            String::new()
        } else {
            format!("exists* {}.{}", binders.join(" "), sep)
        };
        let mut body = if owns.is_empty() {
            "emp".to_string()
        } else {
            owns.join(&format!(" **{}", sep))
        };
        if !props.is_empty() {
            body = format!("{} **{}pure ({})", body, sep, props.join(r" /\ "));
        }
        Ok(format!("{}{}", quant, body))
    }

    fn loop_(
        &mut self,
        cond: &Expr,
        inv: &Exprs,
        requires: &Exprs,
        ensures: &Exprs,
        body: &Stmts,
    ) -> Result<(), String> {
        if !requires.is_empty() || !ensures.is_empty() {
            return Err("a loop with its own `requires` or `ensures`".to_string());
        }
        if self.has_out {
            return Err("a loop in a function with an `_out` parameter".to_string());
        }

        let (binders, owns, props) = self.frame(inv, "a loop")?;

        let before = self.lines.len();
        self.in_guard = true;
        let head = self.inline(cond);
        self.in_guard = false;
        let head = head?;
        if self.lines.len() != before {
            self.lines.truncate(before);
            return Err("a loop whose condition needs a focused access".to_string());
        }

        let outer = std::mem::take(&mut self.lines);
        let was_branch = self.in_branch;
        self.in_branch = true;
        let inits: Vec<bool> = self.slots.iter().map(|s| s.init).collect();
        let r = (|| -> Result<(), String> {
            for s in body.iter() {
                self.stmt(s)?;
            }
            Ok(())
        })();
        self.in_branch = was_branch;
        let body_lines = std::mem::replace(&mut self.lines, outer);
        r?;
        if self.slots.iter().map(|s| s.init).ne(inits) {
            return Err("a loop that first writes a local in its body".to_string());
        }

        self.lines.push(format!("while ({})", head));
        // Pulse is indentation-sensitive and these lines are written out with
        // the statement indent applied only to the first of them, so the
        // continuations carry their own and must sit deeper than `invariant`.
        let quant = if binders.is_empty() {
            String::new()
        } else {
            format!("exists* {}.\n      ", binders.join(" "))
        };
        let mut body = if owns.is_empty() {
            "emp".to_string()
        } else {
            owns.join(" **\n      ")
        };
        if !props.is_empty() {
            body = format!("{} **\n      pure ({})", body, props.join(" /\\ "));
        }
        self.lines.push(format!("  invariant {}{}", quant, body));
        self.divergent = true;
        self.lines.push("{".to_string());
        self.lines.extend(body_lines.iter().map(|l| indent(l)));
        self.lines.push("};".to_string());
        Ok(())
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        match &s.val {
            StmtT::Decl(name, ty) => {
                self.alloc_slot(name, ty)?;
                Ok(())
            }
            StmtT::Let(name, ty, init) => {
                let v = match self.alloc_of(init) {
                    Some((which, pointee)) => self.allocate(name, which, &pointee)?,
                    None => self.rvalue(init)?,
                };
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
                if let (ExprT::Var(v), Some((which, pointee))) =
                    (&strip_vattr(lhs).val, self.alloc_of(rhs))
                {
                    let value = self.allocate(v, which, &pointee)?;
                    return self.store(lhs, &pn, &value);
                }
                let v = self.rvalue(rhs)?;
                self.store(lhs, &pn, &v)
            }
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => {
                self.loop_(cond, inv, requires, ensures, body)?;
                Ok(())
            }
            // A `switch` whose cases all end in `break` reaches the IR as a
            // `Match`; anything with fallthrough or a `return` in a case has
            // already been desugared into flags and `if`s by an earlier pass.
            //
            // Pulse has a `match` on integer literals, and it is what this
            // must use. Desugaring into a chain of `if`s works and is much
            // simpler, but `switch` on sixteen cases then nests sixteen deep,
            // and Pulse infers a join and a frame at every level: one such
            // function took over sixteen minutes on its own. A `match` is
            // flat. `case 1: case 2:` becomes two arms with the same body,
            // which is what C means by it.
            StmtT::Match {
                scrutinee,
                branches,
                default_branch,
                ensures,
            } => {
                let scrut = self.rvalue(scrutinee)?;
                let sty = self.ty_of(scrutinee)?;

                let entry_out = self.out_params.clone();
                let entry_inits: Vec<bool> = self.slots.iter().map(|s| s.init).collect();
                let entry_blocks = self.blocks.clone();
                let restore = |b: &mut Self| {
                    b.blocks = entry_blocks.clone();
                    b.out_params = entry_out.clone();
                    for (slot, init) in b.slots.iter_mut().zip(&entry_inits) {
                        slot.init = *init;
                    }
                };

                let mut arms: Vec<(String, BranchResult)> = Vec::new();
                for br in branches.iter() {
                    for p in br.patterns.iter() {
                        let lit = match &strip_vattr(p).val {
                            ExprT::IntLit(n, _) => int_literal(self.tds, n, &sty)?,
                            ExprT::UnOp(UnOp::Neg, inner) => match &strip_vattr(inner).val {
                                ExprT::IntLit(n, _) => {
                                    int_literal(self.tds, &-(**n).clone(), &sty)?
                                }
                                _ => return Err("a `case` that is not a literal".to_string()),
                            },
                            _ => return Err("a `case` that is not a literal".to_string()),
                        };
                        restore(self);
                        arms.push((format!("({})", lit), self.branch(&br.body)?));
                    }
                }
                restore(self);
                arms.push(("_".to_string(), self.branch(default_branch)?));

                // Every arm has to leave the same state behind, or there is no
                // join. The `default` arm is the one C always has, so it is
                // the reference.
                let (_, last) = arms.last().unwrap();
                let inits = last.inits.clone();
                let outs = last.out_params.clone();
                if arms
                    .iter()
                    .any(|(_, a)| a.inits != inits || a.out_params != outs)
                {
                    return Err(
                        "a `switch` whose cases leave different variables initialised".to_string(),
                    );
                }
                restore(self);
                self.out_params = outs;
                for (slot, init) in self.slots.iter_mut().zip(&inits) {
                    slot.init = *init;
                }

                // Pulse infers the join of an `if` but not of a `match`, so
                // the frame at the join has to be written out. `switch` is the
                // one statement PAL already asks the source to annotate, and
                // that annotation is what goes in the `pure` part.
                let join = self.frame_slprop(ensures, "a `switch`", "      ")?;

                self.lines.push("{".to_string());
                self.lines.push(indent(&format!("match ({}) {{", scrut)));
                for (pat, arm) in &arms {
                    self.lines.push(indent(&indent(&format!("{} -> {{", pat))));
                    self.lines
                        .extend(arm.lines.iter().map(|l| indent(&indent(&indent(l)))));
                    self.lines.push(indent(&indent("}")));
                }
                self.lines.push(indent("};"));
                self.lines.push("}".to_string());
                // Parenthesised because an `exists*` body would otherwise
                // swallow the statement that follows the annotation.
                self.lines.push(format!("ensures ({})", join));
                // Pulse wants a labelled statement to attach the annotation
                // to; without one the parser runs the annotation into
                // whatever follows the `switch`.
                let label = self.fresh("match_join");
                self.lines.push(format!("label {}:;", label));
                Ok(())
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
                ExprT::Free(arg) => self.free(arg),
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
                let nt = self.null_test(cond);
                let c = match nt {
                    Some((i, when)) => Self::null_cond(&self.blocks[i].tmp, when),
                    None => {
                        let cty = self.ty_of(cond)?;
                        if !matches!(self.tds.resolve(&cty).val, TypeT::Bool) {
                            return Err("an `if` on a non-boolean condition".to_string());
                        }
                        self.rvalue(cond)?
                    }
                };

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
                let entry_blocks = self.blocks.clone();
                let live_then = matches!(nt, Some((_, false)));
                if let Some((i, _)) = nt {
                    self.blocks[i].checked = live_then;
                }
                let then = self.branch(then_branch)?;
                let then_blocks = self.blocks.clone();
                self.blocks = entry_blocks.clone();
                self.out_params = entry_out;
                for (slot, init) in self.slots.iter_mut().zip(&entry_inits) {
                    slot.init = *init;
                }
                if let Some((i, _)) = nt {
                    self.blocks[i].checked = !live_then;
                }
                let els = self.branch(else_branch)?;
                let els_blocks = self.blocks.clone();
                self.blocks = entry_blocks;
                if let Some((i, _)) = nt {
                    // The arm that owns the block has to give it back, or the
                    // two arms leave different frames behind and there is
                    // nothing to join.
                    let live = if live_then { &then_blocks } else { &els_blocks };
                    if !live[i].freed {
                        return Err(format!(
                            "an `if` whose non-null arm does not free `{}`",
                            live[i].var
                        ));
                    }
                    self.blocks[i].freed = true;
                    self.blocks[i].checked = false;
                }
                if then.inits != els.inits || then.out_params != els.out_params {
                    return Err(
                        "an `if` whose branches leave different variables initialised".to_string(),
                    );
                }
                self.out_params = then.out_params.clone();
                for (slot, init) in self.slots.iter_mut().zip(&then.inits) {
                    slot.init = *init;
                }

                let (then_pre, else_pre) = match nt {
                    Some((i, null_when_true)) => {
                        let (n, l) = self.null_test_arms(i);
                        if null_when_true { (n, l) } else { (l, n) }
                    }
                    None => (Vec::new(), Vec::new()),
                };
                self.lines.push(format!("if ({})", c));
                self.lines.push("{".to_string());
                self.lines.extend(then_pre.iter().map(|l| indent(l)));
                self.lines.extend(then.lines.iter().map(|l| indent(l)));
                self.lines.push("} else {".to_string());
                self.lines.extend(else_pre.iter().map(|l| indent(l)));
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
                    // A test of a freshly allocated pointer is the one
                    // condition that is not just a value: it decides which arm
                    // owns the block, so each arm opens by eliminating the
                    // guard in the direction the test settled.
                    let nt = self.null_test(cond);
                    let c = match nt {
                        Some((i, when)) => Self::null_cond(&self.blocks[i].tmp, when),
                        None => {
                            let cty = self.ty_of(cond)?;
                            if !matches!(self.tds.resolve(&cty).val, TypeT::Bool) {
                                return Err("an `if` on a non-boolean condition".to_string());
                            }
                            self.rvalue(cond)?
                        }
                    };
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
                    let (mut null_arm, mut live_arm) = match nt {
                        Some((i, _)) => {
                            let (n, l) = self.null_test_arms(i);
                            (n, l)
                        }
                        None => (Vec::new(), Vec::new()),
                    };
                    let (then_pre, else_pre) = match nt {
                        Some((_, true)) => {
                            (std::mem::take(&mut null_arm), std::mem::take(&mut live_arm))
                        }
                        Some((_, false)) => {
                            (std::mem::take(&mut live_arm), std::mem::take(&mut null_arm))
                        }
                        None => (Vec::new(), Vec::new()),
                    };
                    let live_then = matches!(nt, Some((_, false)));
                    let entry_blocks = self.blocks.clone();
                    if let Some((i, _)) = nt {
                        self.blocks[i].checked = live_then;
                    }
                    let (then_lines, then_val) = self.tail_arm(&then_stmts)?;
                    self.blocks = entry_blocks.clone();
                    if let Some((i, _)) = nt {
                        self.blocks[i].checked = !live_then;
                    }
                    let (else_lines, else_val) = self.tail_arm(&else_stmts)?;
                    self.blocks = entry_blocks;
                    let then_lines: Vec<String> = then_pre.into_iter().chain(then_lines).collect();
                    let else_lines: Vec<String> = else_pre.into_iter().chain(else_lines).collect();
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
    match &peel(tds, ty).val {
        TypeT::Int { signed, width } => {
            let suffix = int_suffix(*signed, *width)?;
            if *n < BigInt::ZERO {
                if !*signed {
                    // C converts a negative constant to an unsigned type by
                    // reducing it modulo the width -- `(uint32_t)-1` is
                    // `4294967295` -- and F* has no negative unsigned literal
                    // to write it with, so the reduction is done here.
                    let m = BigInt::from(1u8) << *width;
                    let r = ((n % &m) + &m) % &m;
                    return Ok(format!("{}{}", r, suffix));
                }
                Ok(format!("({}{})", n, suffix))
            } else {
                Ok(format!("{}{}", n, suffix))
            }
        }
        TypeT::SizeT => Ok(format!("{}sz", n)),
        // `true` and `false` are macros for the integer literals 1 and 0, so
        // they reach the IR as literals at type `_Bool`.
        TypeT::Bool => Ok(if *n == BigInt::ZERO { "false" } else { "true" }.to_string()),
        // `NULL` is the integer literal `0` at a pointer type. Any other
        // integer at a pointer type is manufacturing an address, which the
        // model deliberately does not let a program do.
        TypeT::Pointer(..) | TypeT::FnPtr { .. } if *n == BigInt::ZERO => Ok("null".to_string()),
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
        // `size_t` and the signed types have no direct cast either way, so
        // both go through `uint64_t`. C says both directions reduce modulo the
        // target's range, and that is what the composite does.
        (
            TypeT::SizeT,
            TypeT::Int {
                signed: true,
                width,
            },
        ) => Ok(format!(
            "(FStar.Int.Cast.uint64_to_int{} (FStar.SizeT.sizet_to_uint64 {}))",
            width, v
        )),
        (
            TypeT::Int {
                signed: true,
                width,
            },
            TypeT::SizeT,
        ) => Ok(format!(
            "(sizet_of_uint64 (FStar.Int.Cast.int{}_to_uint64 {}))",
            width, v
        )),
        (TypeT::Bool, TypeT::SizeT) => Ok(format!("(if {} then 1sz else 0sz)", v)),
        (TypeT::SizeT, TypeT::Bool) => Ok(format!("(not ({} `SizeT.eq` 0sz))", v)),
        // A pointer is true exactly when it is not null, which is the one
        // question the model lets a program ask about an address it does not
        // own.
        (TypeT::Pointer(..) | TypeT::FnPtr { .. }, TypeT::Bool) => {
            Ok(format!("(not (is_null {}))", v))
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
    let t = peel(tds, ty);
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
        // C requires the shift count to be below the width, which PAL turns
        // into a proof obligation and the source discharges with a
        // `_requires`; a signed left shift additionally needs a non-negative
        // operand. Both come out of the contract, so an untranslated one has
        // to refuse rather than emit a failure about something else.
        BinOp::Shl | BinOp::Shr if matches!(t.val, TypeT::Int { .. }) => {
            if !signed_ok {
                return Err(
                    "a shift, whose width obligation needs the untranslated `_requires`"
                        .to_string(),
                );
            }
            return Ok(format!(
                "`{}.shift_{}`",
                m,
                if matches!(op, BinOp::Shl) {
                    "left"
                } else {
                    "right"
                }
            ));
        }
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

/// A translated body: its lines, and whether it needs the `divergent`
/// qualifier on the enclosing `fn`.
struct TranslatedBody {
    lines: Vec<String>,
    divergent: bool,
    /// The functions in this file the body calls, which is what fixes the
    /// order they have to be written out in.
    uses: HashSet<String>,
}

/// Translate a function body, or say why not. `env` must already have the
/// function's parameters pushed.
fn emit_body(
    tds: &Typedefs,
    env: Env,
    defn: &FnDefn,
    sig: &FnSurface,
    callees: &HashMap<String, Callee>,
    forbidden: &HashSet<String>,
) -> Result<TranslatedBody, String> {
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
        in_guard: false,
        arrays,
        requires_ok: sig.contract && !defn.decl.requires.is_empty(),
        owned: &sig.owned,
        has_out: defn.decl.args.iter().any(|a| a.mode == ParamMode::Out),
        divergent: false,
        blocks: Vec::new(),
        uses: HashSet::new(),
        forbidden,
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
    Ok(TranslatedBody {
        lines: b.lines,
        divergent: b.divergent,
        uses: b.uses,
    })
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
