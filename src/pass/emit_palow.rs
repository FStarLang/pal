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
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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
    /// A `_refine` written on the field, rendered as an F\* proposition about
    /// a binder named `v`, when the translation covers it.
    ///
    /// A field refinement is an invariant of the struct *type*: every value of
    /// it, anywhere, has the property. Stating it in a contract only reaches
    /// parameters, so instead it goes on the field's type in the generated
    /// record, where nothing can construct a value without it. `None` means
    /// there is none, or that it is one of the kinds this does not cover --
    /// an ownership refinement, or one naming a sibling field.
    inv: Option<String>,
}

/// Whether a value of this type can be read out of memory in one step, which
/// is what a whole-struct `_read` needs of every field.
fn readable_field(tds: &Typedefs, ty: &Type) -> bool {
    match &peel(tds, ty).val {
        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
            tds.structs.get(&*n.val).is_some_and(|si| si.has_read)
        }
        TypeT::TypeRef(TypeRefKind::Union(_)) => false,
        // An array field is read element by element, by the recursion the
        // struct's own module generates beside the one that fills it.
        TypeT::FixedArray(..) => {
            flat_array(tds, ty).is_some_and(|(t, _)| palow_name(tds, t).is_some())
        }
        _ => palow_name(tds, ty).is_some(),
    }
}

/// The largest struct that gets a byte-level view. See `has_bytes`.
const MAX_BYTE_LEVEL_FIELDS: usize = 16;

/// How a struct field is owned. A scalar or nested struct field is one
/// points-to; a fixed-size array field is a whole `array_pts_to`, because in C
/// `T f[N]` inside a struct is N elements of storage and not a pointer.
enum FieldShape {
    One {
        pn: String,
    },
    Array {
        pn: String,
        esize: u64,
        len: u64,
    },
    /// A flexible array member: owned exactly as an array field is, but with
    /// the length in the value instead of in the type. That is the whole of
    /// what makes it flexible -- the object is larger than its type says, and
    /// nothing but the value records by how much.
    Flex {
        pn: String,
        esize: u64,
    },
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
            FieldShape::Flex { .. } => format!("Seq.seq {}", elem),
        }
    }

    fn pts_to(&self, at: &str, value: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_pts_to {} p {}", pn, at, value),
            FieldShape::Array { pn, esize, .. } | FieldShape::Flex { pn, esize } => {
                format!("array_pts_to {}_repr {} {} p {}", pn, esize, at, value)
            }
        }
    }

    /// How many bytes of the object the field occupies.
    fn size(&self, tds: &Typedefs, ty: &Type) -> Option<u64> {
        match self {
            FieldShape::One { .. } => palow_sizeof(tds, ty),
            FieldShape::Array { esize, len, .. } => Some(esize * len),
            // A flexible array member contributes no bytes to the type: the
            // object it belongs to is larger than `sizeof` says, and by how
            // much is not a fact about the type at all.
            FieldShape::Flex { .. } => Some(0),
        }
    }

    /// The predicate relating a value of the field's type to the bytes under
    /// it. A scalar publishes one under its own name; an array has no single
    /// name for it, so the same thing is spelled with the array combinator
    /// applied to its element's.
    fn repr_of(&self, v: &str, b: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_repr {} {}", pn, v, b),
            FieldShape::Array { pn, esize, .. } | FieldShape::Flex { pn, esize } => {
                format!("array_repr {}_repr {} {} {}", pn, esize, v, b)
            }
        }
    }

    /// `_pts_to` at an explicit permission.
    fn pts_to_at(&self, a: &str, p: &str, v: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_pts_to {} {} {}", pn, a, p, v),
            FieldShape::Array { pn, esize, .. } | FieldShape::Flex { pn, esize } => {
                format!("array_pts_to {}_repr {} {} {} {}", pn, esize, a, p, v)
            }
        }
    }

    fn uninit_at(&self, a: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_pts_to_uninit {}", pn, a),
            FieldShape::Array { pn, esize, len } => {
                format!("array_pts_to_uninit {}_repr {} {} {}", pn, esize, len, a)
            }
            FieldShape::Flex { .. } => NO_FLEX_STORAGE.to_string(),
        }
    }

    /// Bytes in, ownership out.
    fn conceal(&self, a: &str, p: &str, b: &str, v: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_conceal {} #{} #{} #{};", pn, a, p, b, v),
            FieldShape::Array { pn, esize, .. } | FieldShape::Flex { pn, esize } => format!(
                "array_conceal {}_repr {} {}sz #{} #{} #{};",
                pn, a, esize, p, b, v
            ),
        }
    }

    /// Ownership in, bytes out.
    fn reveal(&self, a: &str, p: &str, v: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_reveal {} #{} #{};", pn, a, p, v),
            FieldShape::Array { pn, esize, .. } | FieldShape::Flex { pn, esize } => {
                format!("array_reveal {}_repr {} {}sz #{} #{};", pn, a, esize, p, v)
            }
        }
    }

    /// Bytes of the right length in, storage out.
    fn claim_uninit(&self, a: &str, b: &str) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_claim_uninit {} #{};", pn, a, b),
            FieldShape::Array { pn, esize, len } => format!(
                "array_claim_all_uninit {}_repr {} {}sz {}sz #{};",
                pn, a, esize, len, b
            ),
            FieldShape::Flex { .. } => format!("{} {} {};", NO_FLEX_STORAGE, a, b),
        }
    }

    /// Storage in, a value out. An array is filled element by element, by the
    /// recursion the enclosing module already generates for its fields.
    fn write_fn(&self) -> String {
        match self {
            FieldShape::One { pn } => format!("{}_write_uninit", pn),
            FieldShape::Array { pn, esize, len } => {
                format!("{}_fill", fill_name(pn, *esize, *len))
            }
            FieldShape::Flex { .. } => NO_FLEX_STORAGE.to_string(),
        }
    }

    fn write_uninit(&self, a: &str, v: &str) -> String {
        format!("{} {} {};", self.write_fn(), a, v)
    }

    /// The write-only view of the field's storage. An array's is the whole
    /// array as storage: `array_pts_to_uninit` hides the element sequence, so
    /// that like every other field's view it is a predicate on the address
    /// and the length alone.
    fn uninit(&self, at: &str) -> Option<String> {
        match self {
            FieldShape::One { pn } => Some(format!("{}_pts_to_uninit {}", pn, at)),
            FieldShape::Array { pn, esize, len } => Some(format!(
                "array_pts_to_uninit {}_repr {} {} {}",
                pn, esize, len, at
            )),
            // No storage view, so the struct as a whole gets none either:
            // there is no such thing as an uninitialised `struct vec`,
            // because how much storage that would be is not known.
            FieldShape::Flex { .. } => None,
        }
    }
}

/// The name a flexible array member's missing storage operations are
/// spelled with. None of them is reachable -- a struct with one has no
/// byte-level view and no uninitialised view, which is what gates them --
/// and if one ever became reachable this is a name F* will not resolve,
/// which is the loud failure such a hole deserves.
const NO_FLEX_STORAGE: &str = "flexible_array_member_has_no_storage_view";

/// The element type of a flexible array member.
fn flex_elem<'a>(tds: &'a Typedefs, ty: &'a Type) -> Option<&'a Type> {
    match &peel(tds, ty).val {
        TypeT::FlexArray(t) => Some(t),
        _ => None,
    }
}

/// How a struct field is owned, or `None` if the model does not cover it.
fn field_shape(tds: &Typedefs, ty: &Type) -> Option<FieldShape> {
    if let Some(t) = flex_elem(tds, ty) {
        if !has_repr(tds, t) {
            return None;
        }
        return Some(FieldShape::Flex {
            pn: palow_name(tds, t)?,
            esize: palow_sizeof(tds, t)?,
        });
    }
    match flat_array(tds, ty) {
        Some((t, n)) => {
            if !has_repr(tds, t) {
                return None;
            }
            Some(FieldShape::Array {
                pn: palow_name(tds, t)?,
                esize: palow_sizeof(tds, t)?,
                len: n,
            })
        }
        None => Some(FieldShape::One {
            pn: palow_name(tds, ty)?,
        }),
    }
}

/// The F* type of a struct field's value.
fn field_type(tds: &Typedefs, ty: &Type) -> Option<String> {
    let elem = match (flex_elem(tds, ty), flat_array(tds, ty)) {
        (Some(t), _) => fstar_type(tds, t)?,
        (None, Some((t, _))) => fstar_type(tds, t)?,
        (None, None) => fstar_type(tds, ty)?,
    };
    Some(field_shape(tds, ty)?.value_type(&elem))
}

/// Where a bit-field sits inside its storage unit, which is everything the
/// emitter needs to read or write it once the unit is in hand.
#[derive(Clone, PartialEq, Eq)]
struct BitPos {
    /// The unit's width in bits, which picks the `Bits` wrapper to call.
    unit_bits: u32,
    off: u32,
    width: u32,
    /// A `_Bool` bit-field is a `bool` and not an integer, so it reads and
    /// writes through the one-bit wrappers instead.
    boolean: bool,
}

impl BitPos {
    /// The value of the bit-field, given the unit's value.
    fn get(&self, u: &str) -> String {
        if self.boolean {
            format!("(Bits.getb{} {} {})", self.unit_bits, u, self.off)
        } else {
            format!(
                "(Bits.get{} {} {} {})",
                self.unit_bits, u, self.off, self.width
            )
        }
    }

    /// The unit's new value, given its old one and the value stored.
    fn put(&self, u: &str, v: &str) -> String {
        if self.boolean {
            format!("(Bits.putb{} {} {} {})", self.unit_bits, u, self.off, v)
        } else {
            format!(
                "(Bits.put{} {} {} {} {})",
                self.unit_bits, u, self.off, self.width, v
            )
        }
    }
}

/// A bit-field of a struct: the synthetic field holding its storage unit,
/// and its position inside it.
#[derive(Clone)]
struct BitField {
    unit: String,
    pos: BitPos,
}

impl BitField {
    /// The Palow type of the storage unit, which is an unsigned integer of
    /// the unit's width whatever the bit-fields inside it are declared as.
    fn unit_pn(&self) -> String {
        format!("uint{}_t", self.pos.unit_bits)
    }
}

/// If `ty` is a struct with a bit-field called `f`, where that bit-field
/// sits. A bit-field is not among the struct's fields: it has no storage of
/// its own, only a position in the unit it shares.
fn bitfield_at<'a>(tds: &'a Typedefs, ty: &Type, f: &str) -> Option<&'a BitField> {
    let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(tds, ty).val else {
        return None;
    };
    tds.structs
        .get(&*n.val.to_string())?
        .bitfields
        .iter()
        .find(|(n2, _)| n2 == f)
        .map(|(_, b)| b)
}

/// The value of field `f` of the struct value `x`, where `bty` is the
/// struct's type. An ordinary field is a projection; a bit-field is the bits
/// it occupies of the unit's value.
fn field_value(tds: &Typedefs, bty: &Type, x: &str, f: &str) -> String {
    match bitfield_at(tds, bty, f) {
        Some(b) => b.pos.get(&format!("({}).fld_{}", x, b.unit)),
        None => format!("({}).fld_{}", x, f),
    }
}

/// A struct the emitter generated a Palow type for. Only structs whose every
/// field has a Palow type get one; the rest stay unknown and any function that
/// mentions them is skipped, as before.
struct StructInfo {
    fields: Vec<StructField>,
    /// The bit-fields, by name. They are not in `fields`: a bit-field has no
    /// storage of its own, so what the struct's value records is the unit,
    /// and the bit-field is a function of it.
    bitfields: Vec<(String, BitField)>,
    size: u64,
    align: u64,
    /// Whether the struct got a whole-object `_read`, which needs every field
    /// to have one. A union has none -- reading one would mean branching on a
    /// ghost tag in a real function -- so a struct containing one cannot be
    /// read as a value either, only field by field.
    has_read: bool,
    /// Whether the struct also got a byte-level `_repr`, and with it the
    /// `_reveal`/`_conceal` pair that makes it usable as an array element or a
    /// union member. A struct earns one when every field has one and sits at a
    /// byte offset, which is what lets the proof carve the object into its
    /// fields and the padding between them and put it back together.
    has_bytes: bool,
}

/// One member of a union the emitter generated a Palow type for.
struct UnionMember {
    name: String,
    ty: Rc<Type>,
    /// How the member is owned. An array arm is the type-punning idiom --
    /// `union { uint8_t bytes[4]; uint32_t word; }` -- so it is not an odd
    /// corner but the reason a union has a byte-level representation at all.
    shape: FieldShape,
    /// The member's own size, which is where the bytes it does not cover
    /// begin. C says a union is as large as its largest member, so every
    /// shorter member leaves a tail that ownership still has to account for.
    size: u64,
}

/// A union the emitter generated a Palow type for. Unlike a struct, a union
/// gets a byte-level `_repr`: its members overlap, so there is no field-wise
/// conjunction to define it as, and going through the bytes is the only
/// definition that makes storing through one member observable through
/// another. That is the whole reason Palow exists, and it is why a union --
/// unlike a generated struct -- can be an array element.
struct UnionInfo {
    members: Vec<UnionMember>,
    size: u64,
    align: u64,
}

struct Typedefs<'a> {
    typedefs: HashMap<&'a str, &'a Rc<Type>>,
    structs: HashMap<String, StructInfo>,
    unions: HashMap<String, UnionInfo>,
    /// The size and alignment clang reports for every aggregate in the file,
    /// including the ones Palow declines to model. A `sizeof` is a number
    /// from the target ABI and does not need a representation: a union with a
    /// `double` arm has no `_pts_to` here, but its size is still the size
    /// clang would compile, and a contract may say so.
    aggregate_layouts: HashMap<String, (u64, u64)>,
    /// Structs declared `_plain`. The annotation says the struct's ownership
    /// is the author's business and not the generator's, so no `_own`
    /// predicate is made for one: whatever it owns is written by hand in a
    /// `_refine`, and a generated conjunct beside it would be claiming the
    /// same memory twice.
    plain_structs: HashSet<String>,
    /// The `_refine` chain written on each struct declaration that carries
    /// one, keyed by struct name.
    ///
    /// A refinement on a *type* is an invariant every value of it satisfies,
    /// so it belongs to every parameter of that type rather than to the
    /// object's ownership: it is a fact about the value, and stating it where
    /// the parameter's own refinements are stated is what makes it hold for a
    /// by-value struct -- which has no ownership at all, and for which the
    /// refinement is the only thing its contract could say.
    refined_structs: HashMap<String, Rc<Type>>,
    /// Whether hand-written Pulse from `_ghost_stmt`, `_inline_pulse` and
    /// `_include_pulse` is spliced into the output. A test whose fragments are
    /// written against the old memory model marks itself beside its source,
    /// and they are dropped instead -- the same weakening the emitter already
    /// reports for anything it cannot translate.
    splice_inline: bool,
    /// Whether that marker was `palow-model-specific` rather than
    /// `palow-old-annotations`: the fragment names something this model does
    /// not have *by design*, so the resulting admit is a floor and not a
    /// backlog item. The two say so differently in the generated file, because
    /// otherwise the census counts them as one thing.
    model_specific: bool,
    /// `_pure` functions that were successfully emitted as F* definitions, and
    /// so may appear in a specification and in a body without being sequenced.
    pure_fns: HashSet<String>,
    /// The definition of each single-argument `_letimpure` accessor: the
    /// formal's name and the expression it stands for. An accessor whose
    /// value the contract does not already bind can still be read by
    /// substituting the actual argument into that expression.
    impure_bodies: HashMap<String, (String, Rc<Expr>)>,
    /// The globals this module publishes an `addr_var_<name>` for. A global's
    /// address is a closed term, so it may appear in another global's
    /// initialiser -- `uint32_t *const p = &g;` -- and that is the only way a
    /// pointer global gets a published value.
    global_addrs: HashSet<String>,
    /// Types declared with `_type`: their definition is a hand-written F* type
    /// expression, so the model has nothing to say about them beyond passing
    /// them through.
    opaque_types: HashSet<String>,
    /// `_let` definitions whose result is an slprop. A call to one is
    /// ownership rather than a fact, so it belongs beside the points-to
    /// predicates rather than inside a `pure`.
    slprop_lets: HashSet<String>,
    /// `_letimpure` accessors, with the F* type of their result. There is no
    /// F* definition to call -- they are impure by construction -- but a call
    /// to one in a contract still denotes something: the ghost value a
    /// `_refine_value` on the argument binds. See `Spec::value`.
    impure_lets: HashMap<String, String>,
}

impl<'a> Typedefs<'a> {
    /// The size and alignment clang reports for an aggregate, whether or not
    /// Palow models it.
    fn aggregate_layout(&self, key: &str) -> Option<(u64, u64)> {
        self.aggregate_layouts.get(key).copied()
    }

    /// Why a fragment was not spliced, phrased so the two markers stay
    /// distinguishable in a census of the generated files.
    fn no_splice(&self) -> String {
        if self.model_specific {
            "inline Pulse for a model this one deliberately does not have".to_string()
        } else {
            "inline Pulse written for the old memory model".to_string()
        }
    }

    fn new(tu: &'a TranslationUnit, splice_inline: bool, model_specific: bool) -> Self {
        let mut m = HashMap::new();
        for decl in &tu.decls {
            if let DeclT::Typedef(td) = &decl.val {
                m.insert(&*td.name.val, &td.body);
            }
        }
        Typedefs {
            typedefs: m,
            splice_inline,
            model_specific,
            structs: HashMap::new(),
            unions: HashMap::new(),
            aggregate_layouts: HashMap::new(),
            plain_structs: tu
                .decls
                .iter()
                .filter_map(|d| match &d.val {
                    DeclT::StructDefn(sd) if is_plain_chain(&sd.refines) => {
                        Some(sd.name.val.to_string())
                    }
                    // `_plain` is as often written on the typedef that names
                    // the struct as on the struct itself, and it says the same
                    // thing: the two are one object, so suppressing the
                    // generated ownership for one suppresses it for both.
                    DeclT::Typedef(td) if is_plain_chain(&td.body) => {
                        match &strip_annotations(&td.body).val {
                            TypeT::TypeRef(TypeRefKind::Struct(n)) => Some(n.val.to_string()),
                            _ => None,
                        }
                    }
                    _ => None,
                })
                .collect(),
            refined_structs: tu
                .decls
                .iter()
                .filter_map(|d| match &d.val {
                    DeclT::StructDefn(sd)
                        if matches!(
                            sd.refines.val,
                            TypeT::Refine(..) | TypeT::RefineAlways(..) | TypeT::RefineUninit(..)
                        ) =>
                    {
                        Some((sd.name.val.to_string(), sd.refines.clone()))
                    }
                    _ => None,
                })
                .collect(),
            pure_fns: HashSet::new(),
            impure_bodies: HashMap::new(),
            opaque_types: tu
                .decls
                .iter()
                .filter_map(|d| match &d.val {
                    DeclT::OpaqueTypeDecl(t) => Some(t.name.val.to_string()),
                    _ => None,
                })
                .collect(),
            slprop_lets: HashSet::new(),
            impure_lets: HashMap::new(),
            global_addrs: tu
                .decls
                .iter()
                .filter_map(|d| match &d.val {
                    DeclT::GlobalVar(g) if !g.is_enum_constant && !global_var_is_array(g) => {
                        Some(g.name.val.to_string())
                    }
                    _ => None,
                })
                .collect(),
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
/// The element type and total length of an array type, flattened.
///
/// At byte level a `T[3][4]` *is* twelve contiguous `T`s. C lays the rows out
/// end to end with no padding between them, so a nested representation would
/// describe exactly the same bytes as the flat one at the cost of a second
/// notion of element. The flat one is the truth this model is built on, and
/// `arr[i][j]` is then the ordinary subscript `arr[i * 4 + j]`.
fn flat_array<'b>(tds: &'b Typedefs, ty: &'b Type) -> Option<(&'b Type, u64)> {
    let TypeT::FixedArray(t, n) = &peel(tds, ty).val else {
        return None;
    };
    Some(match flat_array(tds, t) {
        Some((e, m)) => (e, m * n),
        None => (t, *n),
    })
}

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
    /// Where in the C source this module came from. An IDE pointed at the
    /// output needs to get from a generated file back to the declaration that
    /// produced it; the mapping is per declaration rather than per token,
    /// which is all a one-module-per-declaration layout can offer and enough
    /// to navigate by.
    pub origin: Option<Origin>,
}

/// The C declaration a generated module stands for.
fn origin_of(decl: &Decl) -> Option<Origin> {
    let loc = decl.loc.location();
    Some(Origin {
        file: loc.file_name.clone(),
        range: loc.range,
        name: crate::pass::emit::decl_name(decl),
    })
}

/// The C declaration a generated module stands for.
#[derive(Clone)]
pub struct Origin {
    pub file: Rc<str>,
    pub range: crate::ir::Range,
    pub name: String,
}

/// One declaration's worth of generated code, before it is wrapped in a
/// module. Palow used to emit a single file per translation unit, which was
/// enough to typecheck the specification surface but left a user's
/// `_include_pulse` module nowhere to go: a helper has to be able to sit
/// *between* two generated declarations, naming the first and being named by
/// the second, and that is only expressible if each declaration is its own
/// module. Chunks are produced in an order that is already a valid F*
/// definition order -- it has to be, since the single-module output
/// typechecked -- so the split never has to reorder anything, only decide
/// which earlier modules each one opens.
struct Chunk {
    module: String,
    code: String,
    origin: Option<Origin>,
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

/// The type a declaration's annotation chain wraps.
fn strip_annotations(ty: &Type) -> &Type {
    match &ty.val {
        TypeT::Plain(t)
        | TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Nullable(t) => strip_annotations(t),
        _ => ty,
    }
}

/// Whether a declaration's annotation chain contains `_plain`.
fn is_plain_chain(ty: &Type) -> bool {
    match &ty.val {
        TypeT::Plain(_) => true,
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Nullable(t) => is_plain_chain(t),
        _ => false,
    }
}

fn palow_name(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &tds.resolve(ty).val {
        TypeT::Bool => Some("bool_t".to_string()),
        TypeT::Int { signed, width } => {
            Some(format!("{}int{}_t", if *signed { "" } else { "u" }, width))
        }
        TypeT::SizeT => Some("size_t".to_string()),
        // A float is an object with a size and an object representation, like
        // any other scalar; what is special about it lives in the arithmetic,
        // not in the storage.
        TypeT::Float {
            width: w @ (32 | 64),
        } => Some(format!("float{}_t", w)),
        // On the LP64 target Palow fixes, `ptrdiff_t` *is* `int64_t`, so it
        // shares its storage rather than getting a layer of its own.
        TypeT::PtrdiffT => Some("int64_t".to_string()),
        // Every pointer kind is the same type here; that is the point, and it
        // extends to function pointers: a code address is an address, and
        // making it one reuses the whole storage layer rather than needing a
        // second one.
        TypeT::Pointer(..) | TypeT::FnPtr { .. } => Some("ptr".to_string()),
        TypeT::TypeRef(TypeRefKind::Struct(n)) if tds.structs.contains_key(&*n.val) => {
            Some(format!("struct_{}", n.val))
        }
        TypeT::TypeRef(TypeRefKind::Union(n)) if tds.unions.contains_key(&*n.val) => {
            Some(format!("union_{}", n.val))
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
    if let TypeT::TypeRef(TypeRefKind::Typedef(n)) = &ty.val {
        if tds.opaque_types.contains(&*n.val.to_string()) {
            return Some(format!("Type_{}.ty_{}", n.val, n.val));
        }
    }
    match &tds.resolve(ty).val {
        TypeT::Void => Some("unit".to_string()),
        TypeT::Bool => Some("bool".to_string()),
        TypeT::Int { signed, width } => {
            Some(format!("{}Int{}.t", if *signed { "" } else { "U" }, width))
        }
        TypeT::SizeT => Some("SizeT.t".to_string()),
        TypeT::PtrdiffT => Some("Int64.t".to_string()),
        TypeT::Float {
            width: w @ (32 | 64),
        } => Some(format!("float{}", w)),
        // A specification integer is unbounded, which is what `_let` needs to
        // state a range condition without first having to prove it.
        TypeT::SpecInt => Some("int".to_string()),
        TypeT::SpecNat => Some("nat".to_string()),
        TypeT::Pointer(..) | TypeT::FnPtr { .. } => Some("ptr".to_string()),
        TypeT::TypeRef(TypeRefKind::Struct(n)) if tds.structs.contains_key(&*n.val) => {
            Some(format!("struct_{}", n.val))
        }
        TypeT::TypeRef(TypeRefKind::Union(n)) if tds.unions.contains_key(&*n.val) => {
            Some(format!("union_{}", n.val))
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
    // A generated union always has one: its points-to is defined over its
    // bytes, because overlapping members leave no other choice. A generated
    // struct has one when every one of its fields does -- its points-to stays
    // the conjunction of its fields', and the `_repr` is a second view of the
    // same object, related to the first by a generated proof.
    // `peel` rather than `resolve`: a `_plain struct s` is still a struct, and
    // asking only about typedefs would have said it has a representation.
    if palow_name(tds, ty).is_none() {
        return false;
    }
    match &peel(tds, ty).val {
        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
            tds.structs.get(&*n.val).is_some_and(|si| si.has_bytes)
        }
        _ => true,
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
        // A size is a number from clang's ABI and needs no representation in
        // the model: `sizeof(double)` is answerable even though Palow cannot
        // say what a `double` holds.
        TypeT::Float { width } => Some((*width / 8) as u64),
        TypeT::FixedArray(t, n) => palow_sizeof(tds, t).map(|s| s * n),
        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
            tds.structs.get(&*n.val).map(|s| s.size).or_else(|| {
                tds.aggregate_layout(&format!("struct {}", n.val))
                    .map(|l| l.0)
            })
        }
        TypeT::TypeRef(TypeRefKind::Union(n)) => {
            tds.unions.get(&*n.val).map(|u| u.size).or_else(|| {
                tds.aggregate_layout(&format!("union {}", n.val))
                    .map(|l| l.0)
            })
        }
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
        TypeT::TypeRef(TypeRefKind::Struct(n)) => {
            tds.structs.get(&*n.val).map(|s| s.align).or_else(|| {
                tds.aggregate_layout(&format!("struct {}", n.val))
                    .map(|l| l.1)
            })
        }
        TypeT::TypeRef(TypeRefKind::Union(n)) => {
            tds.unions.get(&*n.val).map(|u| u.align).or_else(|| {
                tds.aggregate_layout(&format!("union {}", n.val))
                    .map(|l| l.1)
            })
        }
        _ => palow_sizeof(tds, ty),
    }
}

/// Whether a parameter type carries a `_refine`, anywhere under the wrappers
/// or through the pointer.
/// The propositions a `_refine` attaches to a parameter's pointee, and whether
/// any of them is of a kind Palow does not translate.
///
/// A `_refine` is a conjunct of the parameter's points-to, so it says
/// something wherever that points-to is stated: on entry where the caller
/// supplies the ownership, and on exit where the callee hands it back. Which
/// of those apply is decided by the parameter's mode, not here.
///
/// `_refine_uninit` is returned separately, in the second component: it holds
/// only while the storage is unwritten, so it belongs beside
/// `<t>_pts_to_uninit` and nowhere else, and a parameter that never has an
/// uninitialised points-to cannot state it at all. A `_refine_value` comes
/// back in the third bucket, together with the name and type it binds: unlike
/// the other two it is not a closed clause, so whoever states it has to
/// produce the value it quantifies over as well.
type Refinements = (
    Vec<Rc<Expr>>,
    Vec<Rc<Expr>>,
    Vec<(Rc<Ident>, Rc<Type>, Rc<Expr>)>,
);

/// Whether a `_refine_uninit` appears strictly below a pointer.
///
/// Where the annotation sits says what storage it is about. Reached through a
/// pointer it describes the pointee's, which is what an `_out` parameter is
/// handed and what any other pointer parameter would be silently dropping.
/// Reached above one it describes the object's own storage -- and a parameter
/// passed by value has none, so there is nothing there to say and nothing
/// lost by not saying it. That is also what the old translator does with it.
fn uninit_below_pointer(tds: &Typedefs, ty: &Type) -> bool {
    match &tds.resolve(ty).val {
        TypeT::Pointer(t, _) => refinements(tds, t).is_ok_and(|(_, u, _)| !u.is_empty()),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, _, _, _)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => uninit_below_pointer(tds, t),
        _ => false,
    }
}

/// The `_refine_always` clauses on a type, which are the only ones that say
/// anything about a parameter whose storage holds no value yet.
fn always_refines(tds: &Typedefs, ty: &Type) -> Vec<Rc<Expr>> {
    match &tds.resolve(ty).val {
        TypeT::RefineAlways(t, p) => {
            let mut v = always_refines(tds, t);
            v.push(p.clone());
            v
        }
        TypeT::Refine(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, _, _, _)
        | TypeT::Plain(t)
        | TypeT::Nullable(t)
        | TypeT::Pointer(t, _) => always_refines(tds, t),
        _ => Vec::new(),
    }
}

fn refinements(tds: &Typedefs, ty: &Type) -> Result<Refinements, String> {
    match &tds.resolve(ty).val {
        TypeT::Refine(t, p) | TypeT::RefineAlways(t, p) => {
            let (mut v, u, b) = refinements(tds, t)?;
            v.push(p.clone());
            Ok((v, u, b))
        }
        TypeT::RefineUninit(t, p) => {
            let (v, mut u, b) = refinements(tds, t)?;
            u.push(p.clone());
            Ok((v, u, b))
        }
        TypeT::RefineValue(t, n, vty, p) => {
            let (v, u, mut b) = refinements(tds, t)?;
            b.push((n.clone(), vty.clone(), p.clone()));
            Ok((v, u, b))
        }
        TypeT::Plain(t) | TypeT::Nullable(t) | TypeT::Pointer(t, _) => refinements(tds, t),
        _ => Ok((Vec::new(), Vec::new(), Vec::new())),
    }
}

/// Turn the `_refine_value`s found on one parameter into the shape the
/// contract builder wants, or record why they cannot be stated.
///
/// The binder gets a name built from the parameter and the name the source
/// chose, so that two parameters refined against the same vocabulary do not
/// collide. A binder whose type has no F* counterpart is the one failure:
/// there is then nothing to quantify over, and a clause mentioning it would
/// be a clause about nothing.
/// One `_refine_value` as the contract builder needs it: the parameter it is
/// written on, that parameter's type, the binder's name and type as the source
/// wrote them, the F* name and type the generated contract will use for it,
/// and the clause.
type RefineValueOn = (
    String,
    Rc<Type>,
    Rc<Ident>,
    Rc<Type>,
    String,
    String,
    Rc<Expr>,
);

fn collect_valued(
    into: &mut Vec<RefineValueOn>,
    err: &mut Option<String>,
    tds: &Typedefs,
    base: &str,
    ty: &Rc<Type>,
    bs: Vec<(Rc<Ident>, Rc<Type>, Rc<Expr>)>,
) {
    for (n, vty, p) in bs {
        match fstar_type(tds, &vty) {
            Some(f) => into.push((
                base.to_string(),
                ty.clone(),
                n.clone(),
                vty.clone(),
                format!("val_{}_{}", base, n.val),
                f,
                p,
            )),
            None => {
                err.get_or_insert(format!(
                    "parameter var_{} is refined against {}, which is {}",
                    base,
                    n.val,
                    describe(tds.resolve(&vty))
                ));
            }
        }
    }
}

/// A refinement predicate that is an `_slprop`-typed fragment of hand-written
/// Pulse, rather than a proposition about the value.
/// Whether a refinement conjunct is ownership rather than a proposition.
///
/// Spliced Pulse says so by its type, and so does a call to an `_slprop`
/// `_let` -- which is the same thing named once and used in several
/// contracts rather than written out at each of them.
fn is_own_refine(tds: &Typedefs, p: &Expr) -> bool {
    match &strip_vattr(p).val {
        ExprT::Cast(inner, to) if matches!(tds.resolve(to).val, TypeT::SLProp) => {
            is_own_refine(tds, inner)
        }
        ExprT::InlinePulse(_, t) => matches!(tds.resolve(t).val, TypeT::SLProp),
        ExprT::FnCall(name, _) => tds.slprop_lets.contains(&*name.val.to_string()),
        _ => false,
    }
}

/// Split a refinement clause into its ownership conjuncts and its
/// propositional ones. Only `&&` is split: a disjunction of ownership is not
/// something this model can state, and it would be dishonest to pretend the
/// conjuncts stood alone.
fn split_refine<'e>(
    tds: &Typedefs,
    p: &'e Expr,
    own: &mut Vec<&'e Expr>,
    props: &mut Vec<&'e Expr>,
) {
    let inner = strip_vattr(p);
    match &inner.val {
        ExprT::Cast(x, to) if matches!(tds.resolve(to).val, TypeT::SLProp) => {
            split_refine(tds, x, own, props)
        }
        ExprT::BinOp(BinOp::LogAnd, l, r) => {
            split_refine(tds, l, own, props);
            split_refine(tds, r, own, props);
        }
        _ if is_own_refine(tds, inner) => own.push(inner),
        _ => props.push(inner),
    }
}

/// Whether a refinement clause states any ownership at all.
fn refine_states_own(tds: &Typedefs, p: &Expr) -> bool {
    let (mut own, mut props) = (Vec::new(), Vec::new());
    split_refine(tds, p, &mut own, &mut props);
    !own.is_empty()
}

fn slprop_refine<'e>(tds: &Typedefs, p: &'e Expr) -> Option<&'e InlinePulseCode> {
    match &strip_vattr(p).val {
        ExprT::Cast(inner, to) if matches!(tds.resolve(to).val, TypeT::SLProp) => {
            slprop_refine(tds, inner)
        }
        ExprT::InlinePulse(code, t) if matches!(tds.resolve(t).val, TypeT::SLProp) => Some(code),
        _ => None,
    }
}

/// The ownership an `_slprop` refinement states.
///
/// The only one PAL writes itself is `_allocated`, which expands to
/// `freeable $(this)`. Matching that shape and rebuilding the term is not a
/// shortcut around splicing: this model's `freeable` carries the size of the
/// block, because "the right to free this" is meaningless without saying how
/// much, and a nullary macro has nowhere to put a `sizeof`. The size is the
/// pointee's, which is exactly what `_allocated` on a `T *` typedef means.
/// Anything else is hand-written and is spliced as written.
fn allocated_own(
    tds: &Typedefs,
    ty: &Type,
    ptr: &str,
    code: &InlinePulseCode,
) -> Result<Option<String>, String> {
    let verbatim: Vec<&str> = code
        .tokens
        .iter()
        .filter_map(|t| match t {
            InlinePulseToken::Verbatim(ct) => Some(ct.text.val.trim()),
            _ => None,
        })
        .filter(|t| !t.is_empty())
        .collect();
    let antiquots = code
        .tokens
        .iter()
        .filter(|t| matches!(t, InlinePulseToken::RValueAntiquot { .. }))
        .count();
    // Not `_allocated` at all: the caller decides what else it could be.
    if verbatim != ["freeable"] || antiquots != 1 {
        return Ok(None);
    }
    let pt = pointee(tds, ty).ok_or("`_allocated` on something that is not a pointer")?;
    let n = palow_sizeof(tds, pt).ok_or_else(|| {
        format!(
            "`_allocated` on a pointer to {}, whose size is not known",
            describe(tds.resolve(pt))
        )
    })?;
    Ok(Some(format!("freeable {} {}sz", ptr, n)))
}

/// Where the pointer goes in a slprop the caller has to restate at a name of
/// its own. Nothing in generated F\* can contain it, so it cannot collide.
const PTR_HOLE: &str = "$PTR$";

/// What a call hands the caller when the callee's return type grants a block.
#[derive(Clone)]
struct RetBlock {
    /// The Palow type name of what the block holds.
    pn: String,
    /// For a `_nullable` return, the slprop the guard encloses, with the
    /// pointer left as `PTR_HOLE`. The caller names it to get past its own
    /// nullness test; a non-nullable return has nothing to get past.
    guarded: Option<String>,
}

/// The Palow type name of what an `_allocated` return type points at, when the
/// contract grants the block to the caller. Both ends read the annotation the
/// same way -- the callee's `ensures` hands the block over, the caller has to
/// take it -- so the two sides agree by asking the same question here.
fn allocated_return(tds: &Typedefs, ty: &Type) -> Option<String> {
    let (ps, _, _) = refinements(tds, ty).ok()?;
    ps.iter().find_map(|p| {
        let code = slprop_refine(tds, p)?;
        allocated_own(tds, ty, "_", code).ok().flatten()
    })?;
    if extent(tds, ty) != Some(Extent::One) {
        return None;
    }
    let pt = pointee(tds, ty)?;
    fstar_type(tds, pt)?;
    palow_name(tds, pt)
}

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
/// is what lets a caller pass `NULL`. `_nullable` is: it says the pointer may
/// be null, which changes *whether* the ownership is there, not what it is of.
/// See `is_nullable`.
fn pointee<'a>(tds: &'a Typedefs, ty: &'a Type) -> Option<&'a Rc<Type>> {
    match &tds.resolve(ty).val {
        // `void *` points at no object: C gives it no size and no
        // representation, so there is nothing for a contract to own through
        // it. That is exactly what `_plain` says about a typed pointer, and
        // it costs nothing here -- in this model every pointer is a `ptr`
        // whatever it points at, so a `void *` needs no conversion in either
        // direction, only the ownership the author supplies by hand.
        TypeT::Pointer(to, _) if matches!(tds.resolve(to).val, TypeT::Void) => None,
        TypeT::Pointer(to, _) => Some(to),
        TypeT::Nullable(t)
        | TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..) => pointee(tds, t),
        _ => None,
    }
}

/// Whether a parameter is `_nullable`, so that what its contract owns is
/// `unless_null p (...)` rather than the points-to itself.
///
/// The wrapper can sit under a refinement, which is why this is a walk rather
/// than a single match. It deliberately does not look through `_plain`: that
/// annotation already says the function owns nothing, so there is nothing for
/// a nullness test to guard.
fn is_nullable(tds: &Typedefs, ty: &Type) -> bool {
    match &tds.resolve(ty).val {
        TypeT::Nullable(_) => true,
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..) => is_nullable(tds, t),
        _ => false,
    }
}

/// A `const` pointer parameter is read-only, so it needs a fraction rather than
/// full ownership. Under Palow this is the *only* thing that distinguishes it:
/// the type is `ptr` either way.
fn is_shared(mode: ParamMode) -> bool {
    matches!(mode, ParamMode::Const)
}

struct FnSurface {
    /// `_out` array parameters: base name -> the term for the sequence of
    /// cells handed in. Their length is the one thing about them a contract
    /// -- including a loop invariant -- can talk about.
    olens: HashMap<String, String>,
    decl: String,
    /// The ownership the contract grants over what the parameters point to.
    /// A function body never has to restate this -- Pulse carries it -- except
    /// at a loop, whose invariant Pulse cannot invent.
    owned: Vec<OwnedParam>,
    /// Parameters whose ownership sits behind a nullness guard.
    guarded: HashSet<String>,
    /// Parameters whose pointee the emitted `requires` really owns. A `_plain`
    /// pointer owns nothing by itself: what ownership it has comes from a
    /// `_refine_value`, and the all-or-nothing contract drop takes that away
    /// with everything else. A body that went on dereferencing one would be
    /// asking Pulse for ownership its own signature no longer states, so the
    /// access is refused and counted instead.
    granted: HashSet<String>,
    /// Whether the contract carries ownership the author wrote by hand. Palow
    /// cannot read such a clause, so it cannot tell which object it covers;
    /// a parameter's dereference already takes one as a grant over everything,
    /// and a *local* holding a pointer the author's clause is about -- a
    /// back-pointer read out of a field, say -- needs the same trust or the
    /// clause is unusable by the code it was written for.
    spliced_own: bool,
    /// Whether the C function's own `_requires`/`_ensures` made it into the
    /// specification. When they did not, the contract we emit is weaker than
    /// the source says, and in particular cannot discharge an overflow
    /// obligation -- see `Body::signed_ok`.
    contract: bool,
    /// The `__fp` wrapper, when this function can be decayed to a code
    /// pointer: the flat, explicitly-quantified form `of_fn_div` needs.
    fp: Option<String>,
    /// How many components that wrapper's witness tuple has, which is the
    /// shape an indirect call has to write out for its holes to be solvable.
    fp_wits: usize,
    /// The mutable globals the contract hands in and back out. The body treats
    /// each as a slot it did not allocate.
    globals: Vec<Slot>,
    /// Modules the contract names, which the body's own uses need not include.
    uses: HashSet<String>,
    /// Parameters whose contract hands in an `is_valid` for the code they
    /// address. Nothing else grants one -- a points-to says where code is, not
    /// what it does -- so this is exactly the set of pointers the body may call
    /// through without knowing which function it is calling.
    valid_fps: HashSet<String>,
    /// Parameters the caller hands over *with* the right to free them: an
    /// `_allocated` pointer taken `_consumes`. The block is the callee's to
    /// return, and a `free` of one is as ordinary as a `free` of a block this
    /// body allocated itself -- the ownership says the same thing either way.
    /// Keyed by the C name; the value is the Palow name of the pointee type
    /// and the element size when the block is an array.
    freeables: HashMap<String, String>,
    /// Parameters whose ownership the caller hands over for good. Whatever
    /// the contract granted at one of these is not wanted back, which is what
    /// decides whether validity gathered at an indirect call has to be put
    /// down again.
    consumed: HashSet<String>,
    /// What a call to this function hands the caller, when its return type
    /// grants a block. The grant is the emitter's reading of an annotation, so
    /// it stands whether or not the author's own clauses translated.
    ret_block: Option<RetBlock>,
    /// Whether the emitted `requires` carries pure facts about the arguments,
    /// from any source. See `Body::requires_ok`.
    req_props: bool,
    /// Whether the return's ownership is the author's own Pulse rather than
    /// the emitter's. Such a clause may enclose anything, including a function
    /// pointer's validity, and the emitter cannot read it to find out -- so
    /// nothing seeded is put down on the way out, and a validity the clause
    /// did not want shows up as a leftover rather than as a missing fact.
    ret_spliced: bool,
    /// The functions whose `__fp` wrapper is named anywhere in the emitted
    /// `ensures`. A validity the postcondition talks about is a validity the
    /// caller receives, so the body must not put it down on the way out.
    post_valid: HashSet<String>,
    /// Set when the signature came out as `fn rec` with a `decreases`, so the
    /// body may call itself. Direct recursion is the only kind: a cycle
    /// through two functions would need them emitted as one mutually
    /// recursive definition, which the per-declaration module layout has
    /// nowhere to put.
    self_rec: bool,
}

/// One parameter's pointee ownership, in the form a loop invariant needs: the
/// C name of the parameter, the F* type of the value, and the points-to less
/// its final value argument.
struct OwnedParam {
    base: String,
    vty: String,
    /// `array_pts_to uint32_t_repr 4 var_a 1.0R ` -- append a value to it.
    pre: String,
    /// What the value was on entry to the *function*. A loop invariant needs
    /// it because `_old` inside one means the same thing it means in an
    /// `_ensures` -- the state the call started in -- and that is a different
    /// value from the one the invariant binds for the current iteration. The
    /// name is the signature's own ghost binder, which is in scope throughout
    /// the body.
    entry: String,
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
    /// Where `_old` names something other than the entry term in `pointees`.
    /// A loop invariant is the case that needs it: the invariant binds a fresh
    /// value for the current iteration, but `_old` still means the state the
    /// *function* was called in, which is the signature's own ghost binder.
    olds: HashMap<String, String>,
    /// Parameters whose `pointees` entry is a sequence rather than a value.
    arrays: HashSet<String>,
    /// Array parameters whose length is known even where their *contents* are
    /// not. An `_out` array has no incoming value, so its `pointees` entry is
    /// `None` on entry -- but it does have a length, because the storage the
    /// caller handed over is a fixed number of cells, and a precondition that
    /// talks about `a._length` is talking about exactly that.
    olens: HashMap<String, String>,
    /// C object -> the term naming its *address*, where it has one. A
    /// parameter is passed by value and a pointer parameter is already an
    /// address, but a local lives in a slot, and `$&(x)` means that slot.
    addrs: HashMap<String, String>,
    /// Struct *value* term -> (the deep-ownership record on entry, on exit).
    ///
    /// Keyed by the value rather than by the parameter because `struct_X_own`
    /// is a predicate about the value, and because that is the one spelling
    /// the two ways of reaching a struct -- by value, or through a pointer,
    /// or as `this` in the struct's own `_refine` -- all agree on.
    owns: HashMap<String, (Option<String>, Option<String>)>,
    /// Parameters whose storage the contract grants only behind a nullness
    /// guard. `_live` on one of these is the claim that the guard is
    /// discharged, which is exactly the claim this model cannot yet make.
    guarded: HashSet<String>,
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
    /// Modules the contract names. A body's uses drive its module's `open`s,
    /// but a contract can name a constant the body never reads -- and does,
    /// whenever the body is admitted.
    uses: RefCell<HashSet<String>>,
    /// Whether signed machine arithmetic may be written out. A specification
    /// generally may not: `Int32.v (a + b)` is not `Int32.v a + Int32.v b`,
    /// and nothing at a contract boundary rules the overflow out. The body of
    /// a `_let` with its own `requires` is the exception -- F* checks that
    /// body under the precondition, which is exactly where the obligation is
    /// discharged.
    signed_ok: bool,
    /// The `_refine_value` bindings in scope, as
    /// `(parameter, F* type of the value, binder, whether a post binder
    /// exists)`. A `_letimpure` accessor over a refined parameter is a way of
    /// naming one of these.
    valued: RefCell<Vec<(String, String, String, bool)>>,
}

impl<'a> Spec<'a> {
    fn int_module(&self, ty: &Type) -> Option<String> {
        int_module(self.tds, ty)
    }

    /// The term for a global this file publishes as a constant, when the name
    /// is one.
    ///
    /// A contract may name a constant for the same reason a body may: nothing
    /// can write it, so there is no state to own and no moment at which to
    /// read it. An enumerator is the extreme case -- it has no storage at all,
    /// so its value is the only thing there is to say about it, and it is
    /// inlined rather than referred to.
    fn global_const(&self, v: &Ident) -> Option<String> {
        let gv = self.env.lookup_global_var(v)?;
        if gv.is_enum_constant {
            let init = gv.init.as_ref()?;
            return const_expr(self.tds, &gv.ty, init);
        }
        if !global_has_value(self.tds, gv) {
            return None;
        }
        self.uses.borrow_mut().insert(format!("Global_{}", v.val));
        Some(format!("var_{}", v.val))
    }

    /// An array global this file published as a sequence constant. Nothing
    /// can write it -- that is what `_pure` says -- so a contract may read it
    /// with no ownership at all, and its refined type carries the length.
    fn global_array_const(&self, v: &Ident) -> Option<String> {
        let gv = self.env.lookup_global_var(v)?;
        if !global_var_is_array(gv) || !gv.is_pure || gv.is_extern {
            return None;
        }
        const_array(self.tds, &gv.ty, gv.init.as_ref()?)?;
        self.uses.borrow_mut().insert(format!("Global_{}", v.val));
        Some(format!("var_{}", v.val))
    }

    fn ty_of(&self, e: &Expr) -> Result<Rc<Type>, String> {
        self.env
            .infer_expr(e)
            .map(|t| t.to_rc())
            .map_err(|_| "a subexpression whose type could not be inferred".to_string())
    }

    /// The name whose storage a `_live` clause is talking about: `_live(s.x)`
    /// and `_live(*p)` are both claims about the slot `s` or `p` names.
    fn live_base(&self, e: &Expr) -> Option<String> {
        match &strip_vattr(e).val {
            ExprT::Var(v) => Some(v.val.to_string()),
            ExprT::Member(b, _) | ExprT::Deref(b) | ExprT::Index(b, _) => self.live_base(b),
            _ => None,
        }
    }

    /// A whole refinement clause: the ownership it states, and the
    /// proposition it states, in the one slprop that is both.
    ///
    /// A refinement is not required to be entirely one or entirely the other.
    /// The natural way to say what a handle is is a conjunction of the two --
    /// "the tag agrees with the ghost state, *and* here is the state" -- and
    /// C has only one conjunction to write it with. So the clause is split on
    /// `&&`, each conjunct is read as whichever of the two it is, and the
    /// result is put back together the way Pulse writes it: the ownership
    /// side by side, the propositions gathered under a single `pure`.
    fn refinement(&self, e: &Expr, w: When) -> Result<String, String> {
        let (mut own, mut props) = (Vec::new(), Vec::new());
        split_refine(self.tds, e, &mut own, &mut props);
        let mut parts = Vec::new();
        for o in own {
            parts.push(match slprop_refine(self.tds, o) {
                Some(code) => self.inline_pulse(code, w)?,
                None => self.value(o, w)?,
            });
        }
        let mut cs = Vec::new();
        for c in props {
            let t = self.prop(c, w)?;
            if t != "True" {
                cs.push(t);
            }
        }
        if !cs.is_empty() {
            parts.push(format!("pure ({})", cs.join(r" /\ ")));
        }
        if parts.is_empty() {
            parts.push("pure True".to_string());
        }
        Ok(parts.join(" ** "))
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
            ExprT::Live(x) => {
                // `_live(x)` says the storage exists. Where the frame already
                // carries it -- a parameter whose points-to the contract
                // states, or a local a loop invariant binds -- the claim has
                // been made and there is nothing left to say. Where it does
                // not, `True` would be an outright weakening: a `_nullable`
                // parameter's storage is behind a guard, and `_live` is
                // precisely the claim that the guard is discharged.
                match self.live_base(x) {
                    Some(b) if self.guarded.contains(&b) => Err(format!(
                        "`_live({})`, whose storage is behind a nullness guard",
                        b
                    )),
                    _ => Ok("True".to_string()),
                }
            }
            ExprT::UnOp(UnOp::Not, inner) => Ok(format!("(~({}))", self.prop(inner, w)?)),
            // A quantified variable is bound at its C type, not at `nat`:
            // `_forall(size_t i, ...)` is a claim about every `size_t`, and
            // binding it that way is what lets every other translation path --
            // `a[i]`, `i < len` -- work unchanged inside the body.
            //
            // The body's well-definedness side conditions stay *inside* the
            // quantifier. `Seq.index` is partial, and the bound that makes it
            // total is normally the quantifier's own antecedent, so hoisting
            // the condition out would both be ill-typed and claim something
            // much stronger than the source does.
            ExprT::Forall(v, ty, body) | ExprT::Exists(v, ty, body) => {
                let all = matches!(&e.val, ExprT::Forall(..));
                let fty = fstar_type(self.tds, ty).ok_or_else(|| {
                    format!("a quantifier over {}", describe(self.tds.resolve(ty)))
                })?;
                let bound = format!("var_{}", v.val);
                let mut env = self.env.clone();
                env.push_var_decl(v, ty.clone(), crate::env::LocalDeclKind::RValue);
                let mut locals = self.locals.clone();
                locals.insert(v.val.to_string(), bound.clone());
                let body = {
                    let inner = Spec {
                        tds: self.tds,
                        env: &env,
                        pointees: self.pointees.clone(),
                        olds: self.olds.clone(),
                        arrays: self.arrays.clone(),
                        olens: self.olens.clone(),
                        owns: self.owns.clone(),
                        addrs: self.addrs.clone(),
                        guarded: self.guarded.clone(),
                        guards: RefCell::new(Vec::new()),
                        ret: self.ret.clone(),
                        locals,
                        uses: RefCell::new(HashSet::new()),
                        signed_ok: false,
                        valued: RefCell::new(Vec::new()),
                    };
                    let p = inner.prop(body, w)?;
                    self.uses
                        .borrow_mut()
                        .extend(inner.uses.borrow().iter().cloned());
                    let g = inner.guards.borrow().join(r" /\ ");
                    if g.is_empty() {
                        p
                    } else if all {
                        format!(r"({} ==> {})", g, p)
                    } else {
                        format!(r"({} /\ {})", g, p)
                    }
                };
                Ok(format!(
                    "({} ({}: {}). {})",
                    if all { "forall" } else { "exists" },
                    bound,
                    fty,
                    body
                ))
            }
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
        // An `_array` *field*'s ownership is a sequence in the struct's
        // ownership record, so its length is there for the asking -- and this
        // is the only place it can come from, since the predicate on purpose
        // does not fix it.
        if let ExprT::Member(b, f) = &strip_vattr(inner).val {
            return Some(
                self.own_field(b, &f.val, w)
                    .map(|o| format!("(Seq.length {})", o)),
            );
        }
        let ExprT::Var(v) = &inner.val else {
            return Some(Err("`_length` of a computed pointer".to_string()));
        };
        // A `_pure` array global is published as a sequence constant rather
        // than as an object, so there is no ownership to read the length off
        // and no need for one: the sequence itself has it, and its refined
        // type fixes it to the literal the initialiser gave.
        if !self.pointees.contains_key(&*v.val)
            && let Some(t) = self.global_array_const(v)
        {
            return Some(Ok(format!("(Seq.length {})", t)));
        }
        Some(match self.pointees.get(&*v.val) {
            None => match self.olens.get(&*v.val) {
                Some(t) => Ok(format!("(Seq.length {})", t)),
                None => Err(format!("`{}._length` in a contract", v.val)),
            },
            Some((pre, post)) => {
                let chosen = match w {
                    When::Post => post,
                    When::Pre | When::Old => pre,
                };
                match chosen.as_ref().or_else(|| self.olens.get(&*v.val)) {
                    Some(s) => Ok(format!("(Seq.length {})", s)),
                    None => Err(format!("`{}._length` is not available here", v.val)),
                }
            }
        })
    }

    /// The sequence or value a struct's deep ownership holds for one of its
    /// fields, at the value the struct has at `w`.
    fn own_field(&self, base: &Expr, f: &str, w: When) -> Result<String, String> {
        let sv = self.value(base, w)?;
        let Some((pre, post)) = self.owns.get(&sv) else {
            return Err(format!(
                "`.{}`, whose ownership the contract does not state",
                f
            ));
        };
        let chosen = match w {
            When::Post => post,
            When::Pre | When::Old => pre,
        };
        match chosen {
            Some(o) => Ok(format!("(({}).own_{})", o, f)),
            None => Err(format!("`.{}` has no value here", f)),
        }
    }

    /// The address of a place, as a specification term.
    ///
    /// A contract can say where an object *is* without owning it, which is
    /// what an aliasing claim needs: `s->p == &s->inline_buf[0]` is a fact
    /// about two addresses. In this model an address is arithmetic on the
    /// pointer the caller passed, so the whole thing is `var_s` plus the
    /// offsets -- no ownership is consulted and none is needed.
    fn addr_of(&self, e: &Expr, w: When) -> Result<String, String> {
        match &strip_vattr(e).val {
            // `&*p` is `p`, and `p->f` is `(*p).f`, so this is where the
            // recursion bottoms out at the pointer the contract already names.
            ExprT::Deref(inner) => self.value(inner, w),
            ExprT::Member(base, f) => {
                let bty = self.ty_of(base)?;
                let sn = palow_name(self.tds, &bty)
                    .ok_or_else(|| "an address inside something with no layout".to_string())?;
                Ok(format!(
                    "({} +! {}_offsetof_{})",
                    self.addr_of(base, w)?,
                    sn,
                    f.val
                ))
            }
            // Only a literal index: the offset is a byte count, and nothing
            // multiplies in a generated module, so a computed one would have
            // to be folded and cannot be.
            ExprT::Index(base, i) => {
                let ExprT::IntLit(n, _) = &strip_casts(i).val else {
                    return Err("an address at a computed index in a contract".to_string());
                };
                let a = self.addr_of(base, w)?;
                let bty = self.ty_of(base)?;
                let es = match &peel(self.tds, &bty).val {
                    TypeT::FixedArray(el, _) | TypeT::FlexArray(el) => palow_sizeof(self.tds, el),
                    _ => pointee(self.tds, &bty)
                        .as_deref()
                        .and_then(|el| palow_sizeof(self.tds, el)),
                }
                .ok_or_else(|| "an address inside a non-array in a contract".to_string())?;
                let off: u64 = u64::try_from(&**n)
                    .map_err(|_| "an address at an index that is not a number".to_string())?;
                match off * es {
                    0 => Ok(a),
                    k => Ok(format!("({} +! {}sz)", a, k)),
                }
            }
            _ => Err(format!("an address of {} in a contract", expr_kind(e))),
        }
    }

    /// `*p` and `p[i]`. For a scalar parameter the pointee *is* the ghost
    /// value; for an array parameter it is an index into the ghost sequence,
    /// which is why the two cannot share a translation.
    fn pointee_at(&self, base: &Expr, idx: Option<&Expr>, w: When) -> Result<String, String> {
        // `*(s->f)` where the contract owns `s` deeply. The deep half already
        // names the value behind every pointer field, so the dereference is a
        // projection out of it rather than something the contract has to be
        // asked for again -- the same route `_length` of such a field takes.
        if idx.is_none()
            && let ExprT::Member(b, f) = &strip_vattr(base).val
        {
            return self.own_field(b, &f.val, w);
        }
        let ExprT::Var(v) = &base.val else {
            return Err("a contract that dereferences a computed pointer".to_string());
        };
        let Some((pre, post)) = self.pointees.get(&*v.val) else {
            return Err(format!("`*{}` in a contract", v.val));
        };
        let old;
        let chosen = match w {
            When::Post => post,
            When::Old if self.olds.contains_key(&*v.val) => {
                old = Some(self.olds[&*v.val].clone());
                &old
            }
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

    /// What has to hold for a partial machine operator to be defined: a shift
    /// count below the width, and no overflow for signed arithmetic. These are
    /// C's own rules, so stating them costs the contract nothing it did not
    /// already owe.
    fn definedness(&self, op: BinOp, ty: &Type, l: &Expr, r: &Expr, w: When) -> Option<String> {
        // `size_t` is unsigned and its F* operations are the checked ones, so
        // what it owes is the same non-overflow C already demands of it.
        if matches!(peel(self.tds, ty).val, TypeT::SizeT) {
            let (a, b) = (self.value(l, w).ok()?, self.value(r, w).ok()?);
            return match op {
                BinOp::Add => Some(format!("SizeT.fits (SizeT.v {} + SizeT.v {})", a, b)),
                BinOp::Sub => Some(format!("SizeT.v {} >= SizeT.v {}", a, b)),
                BinOp::Mul => Some(format!(
                    "SizeT.fits (SizeT.v {} `op_Multiply` SizeT.v {})",
                    a, b
                )),
                _ => None,
            };
        }
        let TypeT::Int { signed, width } = peel(self.tds, ty).val else {
            return None;
        };
        let m = format!("{}Int{}", if signed { "" } else { "U" }, width);
        match op {
            BinOp::Shl | BinOp::Shr => {
                // The count has a type of its own, and F* reads it with that
                // type's `v`.
                let rty = self.ty_of(r).ok()?;
                let TypeT::Int {
                    signed: rs,
                    width: rw,
                } = peel(self.tds, &rty).val
                else {
                    return None;
                };
                let mut g = format!(
                    "{}Int{}.v {} < {}",
                    if rs { "" } else { "U" },
                    rw,
                    self.value(r, w).ok()?,
                    width
                );
                // A shift of a negative signed value is undefined in C, and
                // F* refuses it too.
                if signed {
                    g = format!(r"{} /\ {}.v {} >= 0", g, m, self.value(l, w).ok()?);
                }
                Some(g)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul if signed => Some(format!(
                "FStar.Int.size ({}.v {} {} {}.v {}) {}",
                m,
                self.value(l, w).ok()?,
                match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    _ => "`op_Multiply`",
                },
                m,
                self.value(r, w).ok()?,
                width
            )),
            _ => None,
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
        // A cast from a specification type is the author writing a
        // mathematical integer where C's grammar wants a machine one, and the
        // number they meant is the number it already is. Reading it that way
        // rather than as `SizeT.uint_to_t n` also avoids a typing obligation
        // the clause has no way to discharge: a guard conjoined at the top of
        // the clause cannot mention a variable the clause binds itself, which
        // is exactly where these casts appear.
        if let ExprT::Cast(inner, _) = &strip_vattr(e).val
            && matches!(
                self.tds.resolve(&ty).val,
                TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT
            )
            && let Ok(ity) = self.ty_of(inner)
            && matches!(self.tds.resolve(&ity).val, TypeT::SpecInt | TypeT::SpecNat)
        {
            return self.num(inner, w);
        }
        // Negation is subtraction from zero, so it is undefined on overflow
        // for the same reason and reads mathematically for the same reason.
        if let ExprT::UnOp(UnOp::Neg, inner) = &strip_vattr(e).val
            && matches!(self.tds.resolve(&ty).val, TypeT::Int { signed: true, .. })
        {
            return Ok(format!("(0 - {})", self.num(inner, w)?));
        }
        match self.int_module(&ty) {
            Some(m) => Ok(format!("({}.v {})", m, self.value(e, w)?)),
            None => self.value(e, w),
        }
    }

    /// A specification expression in value position.
    /// A fragment of hand-written Pulse in a contract.
    ///
    /// The same splice as in a body, against the contract's view of the world:
    /// `$(e)` is what the specification says `e` is at this point -- which for
    /// an `_old` or an `_ensures` is not what the body would read -- and `$&(e)`
    /// is the parameter's own address, which a contract can only name for
    /// something it was handed directly.
    fn inline_pulse(&self, code: &InlinePulseCode, w: When) -> Result<String, String> {
        if !self.tds.splice_inline {
            return Err(self.tds.no_splice());
        }
        let mut out = String::new();
        for tok in &code.tokens {
            match tok {
                InlinePulseToken::Verbatim(ct) => {
                    out.push_str(ct.before);
                    out.push_str(&ct.text.val);
                }
                InlinePulseToken::RValueAntiquot { before, expr } => {
                    let v = self.value(expr, w)?;
                    out.push_str(before);
                    out.push_str(&format!("({})", v));
                }
                InlinePulseToken::LValueAntiquot { before, expr } => {
                    let ExprT::Var(v) = &strip_vattr(expr).val else {
                        return Err("`$&` of something a contract cannot address".to_string());
                    };
                    let n = v.val.to_string();
                    out.push_str(before);
                    match self.addrs.get(&n) {
                        Some(a) => out.push_str(&format!("({})", a)),
                        None => out.push_str(&format!("(var_{})", n)),
                    }
                }
                InlinePulseToken::TypeAntiquot { before, ty } => {
                    let t = fstar_type(self.tds, ty)
                        .ok_or_else(|| format!("`$type` of {}", describe(ty)))?;
                    out.push_str(before);
                    out.push_str(&format!("({})", t));
                }
                InlinePulseToken::FieldAntiquot {
                    before,
                    ty,
                    field_name,
                } => {
                    out.push_str(before);
                    out.push_str(&field_antiquot(self.tds, ty, field_name)?);
                }
                InlinePulseToken::AuxFnAntiquot { kind, .. } => {
                    return Err(format!(
                        "`${}`, which names a helper of the old memory model",
                        kind.keyword()
                    ));
                }
                InlinePulseToken::Declare { .. } => {
                    return Err("`$declare` in a contract".to_string());
                }
            }
        }
        flatten_fragment(&out)
    }

    /// The sequence a subscript looks in, and the index it looks at.
    ///
    /// A multidimensional array field is one flat sequence in the record,
    /// exactly as it is one flat run of bytes in memory. `m->arr[1][2]` on an
    /// `int[3][4]` therefore picks element `1 * 4 + 2` of a twelve-element
    /// sequence; the outer subscript is a stride and not a lookup, because
    /// the row it names is not an object of its own.
    fn flat_subscript(&self, e: &Expr, w: When) -> Result<(String, String), String> {
        let ExprT::Index(base, idx) = &strip_vattr(e).val else {
            return Err(format!("a contract that indexes {}", expr_kind_of(&e.val)));
        };
        let i = self.num(idx, w)?;
        let bty = self.ty_of(base)?;
        if matches!(&strip_vattr(base).val, ExprT::Index(..)) {
            let Some((_, width)) = flat_array(self.tds, &bty) else {
                return Err("a contract that indexes an array element".to_string());
            };
            let (seq, outer) = self.flat_subscript(base, w)?;
            // The stride has to be folded away rather than written down: a
            // contract module has no multiplication in scope, and the body
            // that has to agree with this index only translates a constant
            // row for the same reason its arithmetic would otherwise need a
            // `fits` obligation.
            let (Ok(k), Ok(j)) = (outer.parse::<u64>(), i.parse::<u64>()) else {
                return Err(
                    "a contract that indexes a multidimensional array at a variable row"
                        .to_string(),
                );
            };
            return Ok((seq, format!("{}", k * width + j)));
        }
        if !matches!(
            peel(self.tds, &bty).val,
            TypeT::FixedArray(..) | TypeT::FlexArray(..)
        ) {
            return Err(format!(
                "a contract that indexes {}",
                describe(self.tds.resolve(&bty))
            ));
        }
        Ok((self.value(base, w)?, i))
    }

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
                            return self.value(inner, w);
                        }
                        // Otherwise it is a real conversion, and it is the
                        // same one the body would emit -- there is no reason
                        // for a contract to describe a narrowing or a change
                        // of signedness differently from the code it
                        // constrains, and using one function for both is what
                        // keeps the two provably about the same value.
                        let v = self.value(inner, w)?;
                        convert(peel(self.tds, &from), peel(self.tds, to), &v).map_err(|_| {
                            format!(
                                "a contract converting {} to {}",
                                describe(self.tds.resolve(&from)),
                                describe(to)
                            )
                        })
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
                } else if let Some(t) = self.global_const(v) {
                    Ok(t)
                } else if self.pointees.contains_key(&*v.val) && !self.arrays.contains(&*v.val) {
                    // A mutable global is not reached through a pointer, so
                    // its name *is* the object and the value the ownership
                    // conjunct names is what the contract means by it. An
                    // array global is excluded because there the name is a
                    // decayed pointer and not a value at all.
                    self.pointee_at(e, None, w)
                } else {
                    Err(format!("`{}` in a contract", v.val))
                }
            }
            // As in a body: the enclosing structure is the field pointer less
            // the field's offset.
            ExprT::ContainerOf(inner, ty, field) => {
                let TypeT::TypeRef(TypeRefKind::Struct(sname)) = &self.tds.resolve(ty).val else {
                    return Err(format!(
                        "`_container_of` of {}",
                        describe(self.tds.resolve(ty))
                    ));
                };
                if !self.tds.structs.contains_key(&*sname.val) {
                    return Err(format!(
                        "`_container_of` of {}",
                        describe(self.tds.resolve(ty))
                    ));
                }
                let base = self.value(inner, w)?;
                Ok(sub_offset(
                    base,
                    &format!("struct_{}_offsetof_{}", sname.val, field.val),
                ))
            }
            ExprT::Deref(inner) => self.pointee_at(inner, None, w),
            ExprT::Index(base, idx) if matches!(strip_vattr(base).val, ExprT::Var(_)) => {
                self.pointee_at(base, Some(idx), w)
            }
            // An `_array` field's elements are not in the struct's value at
            // all -- the value holds only the pointer -- so the sequence comes
            // from the struct's deep ownership.
            ExprT::Index(base, idx)
                if matches!(&strip_vattr(base).val, ExprT::Member(..))
                    && self
                        .ty_of(base)
                        .is_ok_and(|t| extent(self.tds, &t) == Some(Extent::Array)) =>
            {
                let ExprT::Member(b, f) = &strip_vattr(base).val else {
                    unreachable!()
                };
                let seq = self.own_field(b, &f.val, w)?;
                let i = self.num(idx, w)?;
                self.guards
                    .borrow_mut()
                    .push(format!("{} < Seq.length {}", i, seq));
                Ok(format!("(Seq.index {} {})", seq, i))
            }
            // A fixed-size array *field* is a sequence in the struct's record,
            // so indexing it is `Seq.index` of a projection rather than a
            // lookup in a parameter's own sequence.
            ExprT::Index(..) => {
                let (seq, i) = self.flat_subscript(e, w)?;
                self.guards
                    .borrow_mut()
                    .push(format!("{} < Seq.length {}", i, seq));
                Ok(format!("(Seq.index {} {})", seq, i))
            }
            // `u.m._active` asks which member of a union is the live one.
            // Palow's union value is a tagged sum -- every member is a
            // constructor -- so the question is which constructor it was
            // built with, and the answer is a discriminator applied to the
            // union's own value. Nothing is read: this is a fact about a
            // value the contract already carries.
            ExprT::VAttr(VAttr::Active(m), obj) => {
                let uty = self.ty_of(obj)?;
                let TypeT::TypeRef(TypeRefKind::Union(u)) = &peel(self.tds, &uty).val else {
                    return Err(format!(
                        "`_active` on {} in a contract",
                        describe(self.tds.resolve(&uty))
                    ));
                };
                Ok(format!(
                    "(Union_{}_{}? {})",
                    u.val,
                    m.val,
                    self.value(obj, w)?
                ))
            }
            // A struct value is an F* record, so a field of one is a
            // projection. `s->f` reaches here as `(*s).f`.
            ExprT::Ref(place) => self.addr_of(place, w),
            ExprT::Member(base, f) => {
                let bty = self.ty_of(base)?;
                if palow_name(self.tds, &bty).is_none() {
                    return Err(format!(
                        "a contract that projects a field of {}",
                        describe(self.tds.resolve(&bty))
                    ));
                }
                let bty = self.ty_of(base)?;
                Ok(field_value(
                    self.tds,
                    &bty,
                    &self.value(base, w)?,
                    &f.val.to_string(),
                ))
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
                    // Unsigned negation wraps and is defined, so a contract
                    // can say it and means the same thing a body would.
                    (
                        UnOp::Neg,
                        TypeT::Int {
                            signed: false,
                            width,
                        },
                    ) => Ok(format!(
                        "(0{} `Pulse.Lib.C.UInt{}.sub_wrap` {})",
                        int_suffix(false, *width)?,
                        width,
                        self.value(inner, w)?
                    )),
                    // The bitwise complement is total on the whole unsigned
                    // range, so it needs nothing said about it and is the same
                    // function the body emits.
                    (
                        UnOp::BitNot,
                        TypeT::Int {
                            signed: false,
                            width,
                        },
                    ) => Ok(format!(
                        "(FStar.UInt{}.lognot {})",
                        width,
                        self.value(inner, w)?
                    )),
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
            ExprT::FloatLit(text, ty) => float_literal(self.tds, text, ty),
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
                    let o = match binop(self.tds, *op, &ty, self.signed_ok) {
                        Ok(o) => o,
                        // The operator is partial, and what makes it defined
                        // is a fact the C source states in a `_requires` of
                        // this same contract. A body can lean on that clause
                        // because Pulse puts it in scope; a contract clause
                        // cannot, because F* types the clauses independently.
                        // So the obligation is stated here, in the clause that
                        // needs it, as a conjunct to its own left: `p /\ q`
                        // types `q` with `p` assumed, which is exactly the
                        // scope the application is missing. The clause it
                        // guards is then a stronger statement than C's, and
                        // provable from the `_requires` that motivated it.
                        Err(e) => {
                            let g = self.definedness(*op, &ty, l, r, w).ok_or(e)?;
                            self.guards.borrow_mut().push(g);
                            binop(self.tds, *op, &ty, true)?
                        }
                    };
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
            // Hand-written Pulse as a contract *term*: a pure fact the author
            // states themselves. The slprop-valued case is not here -- an
            // slprop is ownership, not a proposition, and it goes into the
            // `requires` and `ensures` clauses directly rather than under a
            // `pure`.
            ExprT::InlinePulse(code, _) => {
                if !self.tds.splice_inline {
                    return Err(self.tds.no_splice());
                }
                self.inline_pulse(code, w)
            }
            // A `_letimpure` accessor is not a function that can be called in
            // a specification -- it is impure, which is the whole reason it
            // exists. What it denotes, though, is a ghost value the contract
            // already binds: `_elements_of(l)` is the list that `l`'s
            // `_refine_value` quantifies over. So a call to one is read as a
            // mention of that binder, which is both what the author meant and
            // the only thing in scope with the right type.
            //
            // The old model instead emits the accessor as a `ghost fn` with
            // `requires pure False` and calls it inside its `with_pure`
            // notation: a way of writing a value that cannot be computed.
            // Naming the binder is the same value, written directly.
            ExprT::FnCall(name, args)
                if self.tds.impure_lets.contains_key(&*name.val.to_string()) && args.len() == 1 =>
            {
                let want = self.tds.impure_lets[&*name.val.to_string()].clone();
                let base = match &strip_vattr(&args[0]).val {
                    ExprT::Var(v) => v.val.to_string(),
                    _ => {
                        return Err(format!(
                            "`{}` of {} in a contract",
                            name.val,
                            expr_kind(&args[0])
                        ));
                    }
                };
                let valued = self.valued.borrow();
                let hit = valued
                    .iter()
                    .find(|(b, fty, _, post)| {
                        *b == base && *fty == want && (*post || !matches!(w, When::Post))
                    })
                    .map(|(_, _, binder, _)| binder.clone());
                match hit {
                    // The result's ghost value is bound by the `ensures`
                    // itself. There is no earlier state for it to be the
                    // later version of, and nothing to reveal: the
                    // existential is not erased.
                    Some(binder) if base == "return" => Ok(binder),
                    Some(binder) => Ok(match w {
                        When::Post => format!("{}'", binder),
                        _ => format!("(reveal {})", binder),
                    }),
                    // No binder quantifies over it -- but the accessor has a
                    // definition, and if that definition is something a
                    // contract can say, saying it is both what the author
                    // wrote and the only reading there is. `_letimpure` exists
                    // because the value cannot be *computed*, not because it
                    // cannot be *named*.
                    None => match self.tds.impure_bodies.get(&*name.val.to_string()) {
                        Some((formal, body)) => {
                            let inlined = subst_var(body, formal, &args[0]).ok_or_else(|| {
                                format!(
                                    "`{}` of `{}`, which carries no matching `_refine_value`",
                                    name.val, base
                                )
                            })?;
                            self.value(&inlined, w)
                        }
                        None => Err(format!(
                            "`{}` of `{}`, which carries no matching `_refine_value`",
                            name.val, base
                        )),
                    },
                }
            }
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
            // A size is a literal in Palow, so it is the same literal on
            // both sides: the contract states exactly the number the body
            // computes, which is what makes `return == sizeof(int)` provable
            // rather than merely consistent.
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
            _ => Err(format!("{} in a contract", expr_kind(e))),
        }
    }
}

/// The reason string for a function declared here and defined elsewhere. It
/// travels through the same `Result` as a translation failure, and is picked
/// out again where the body is written, because everything in between -- the
/// divergence fixpoint, the call-graph sort -- treats "no body" alike.
const EXTERNAL: &str = "it has no definition here";

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
    // An slprop-valued `_let` is a name for a piece of ownership. Its body is
    // hand-written Pulse -- the model has no other way to spell one -- so this
    // is a pass-through, exactly like a `_type`.
    let slprop = matches!(tds.resolve(&ld.ret_type).val, TypeT::SLProp);
    let ret = if slprop {
        "slprop".to_string()
    } else {
        fstar_type(tds, &ld.ret_type)
            .ok_or_else(|| format!("it returns {}", describe(tds.resolve(&ld.ret_type))))?
    };

    let mut sp = Spec {
        tds,
        env,
        pointees: HashMap::new(),
        olds: HashMap::new(),
        arrays: HashSet::new(),
        olens: HashMap::new(),
        owns: HashMap::new(),
        addrs: HashMap::new(),
        guarded: HashSet::new(),
        guards: RefCell::new(Vec::new()),
        ret: "ret".to_string(),
        locals: HashMap::new(),
        uses: RefCell::new(HashSet::new()),
        signed_ok: false,
        valued: RefCell::new(Vec::new()),
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
    // The body is checked under the `requires`, so signed arithmetic there
    // has somewhere to discharge its overflow obligation -- unlike a
    // contract, which is a claim about a boundary and has nothing.
    sp.signed_ok = !ld.requires.is_empty();
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
        olds: HashMap::new(),
        arrays: HashSet::new(),
        olens: HashMap::new(),
        owns: HashMap::new(),
        addrs: HashMap::new(),
        guarded: HashSet::new(),
        guards: RefCell::new(Vec::new()),
        ret: "ret".to_string(),
        locals: HashMap::new(),
        uses: RefCell::new(HashSet::new()),
        signed_ok: false,
        valued: RefCell::new(Vec::new()),
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

    // The body of a `_let` is checked under its own `requires`, so signed
    // arithmetic there has somewhere to discharge its overflow obligation --
    // unlike a contract, which is a claim about a boundary and has nothing.
    sp.signed_ok = !decl.requires.is_empty();
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

/// Whether a contract clause states *ownership* rather than a proposition.
///
/// A call to an slprop-valued `_let` is the same thing under a name: the
/// author has given a piece of ownership a word, and a contract that uses the
/// word means the ownership.
fn is_slprop_clause(tds: &Typedefs, e: &Rc<Expr>) -> bool {
    match &strip_vattr(e).val {
        ExprT::InlinePulse(_, t) => matches!(tds.resolve(t).val, TypeT::SLProp),
        ExprT::FnCall(n, _) => tds.slprop_lets.contains(&*n.val.to_string()),
        ExprT::Cast(inner, t) if matches!(tds.resolve(t).val, TypeT::SLProp) => {
            matches!(&strip_vattr(inner).val, ExprT::FnCall(n, _) if tds.slprop_lets.contains(&*n.val.to_string()))
        }
        _ => false,
    }
}

/// Build the Pulse declaration for one C function, or explain why we cannot.
fn emit_fn(
    tds: &Typedefs,
    env: &Env,
    decl: &FnDecl,
    globals: &[Slot],
    decay: bool,
) -> Result<FnSurface, String> {
    let name = format!("func_{}", decl.name.val);

    let mut params: Vec<String> = Vec::new();
    let mut ghosts: Vec<String> = Vec::new();
    let mut perms: Vec<String> = Vec::new();
    // The same implicit binders again, as (name, underlying type, erased),
    // because the `__fp` wrapper below cannot have implicits: `valid` relates
    // an address to a *flat* spec, so every one of them has to become a
    // component of the explicit witness the caller passes.
    let mut wits: Vec<(String, String, bool)> = Vec::new();
    // Whether the author's `_ensures` states ownership rather than only
    // propositions. Asked here, ahead of the parameter loop, because it
    // changes what a parameter mode is allowed to promise back.
    let ens_own = decl.ensures.iter().any(|e| is_slprop_clause(tds, e));
    let mut req: Vec<String> = Vec::new();
    // Hand-written ownership the contract hands back, which unlike the
    // generated kind binds no existential of its own -- the author names
    // whatever they need inside the fragment.
    let mut owned_post: Vec<String> = Vec::new();
    let mut preserved: Vec<String> = Vec::new();
    // Ownership handed back with a value the contract may constrain: the
    // existential binder, its type, and the points-to less its value argument.
    // The ownership handed back at exit, as a complete slprop: the binder is
    // substituted here rather than appended later, because a nullable
    // parameter's points-to sits *inside* `unless_null` and so has no hole at
    // the end to append to.
    let mut fresh: Vec<(String, String, String)> = Vec::new();
    let mut pointees: HashMap<String, (Option<String>, Option<String>)> = HashMap::new();
    let mut owned: Vec<OwnedParam> = Vec::new();
    let mut arrays: HashSet<String> = HashSet::new();
    let mut olens: HashMap<String, String> = HashMap::new();
    let mut owns: HashMap<String, (Option<String>, Option<String>)> = HashMap::new();
    // The `_refine`s on each parameter's pointee, to be translated once the
    // pointee terms for the whole signature are known.
    // A `_refine` written on a struct declaration is an invariant of the
    // *type*, so every parameter of it carries the refinement whether or not
    // the parameter itself was annotated. Collecting it beside the
    // parameter's own refinements is what makes it reach the contract, and
    // binding `this` to the struct value is what makes it mean the same thing
    // it means in the declaration.
    let struct_refines = |ty: &Type| -> Vec<Rc<Expr>> {
        let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(tds, ty).val else {
            return Vec::new();
        };
        tds.refined_structs
            .get(&*n.val.to_string())
            .and_then(|r| refinements(tds, r).ok())
            .map(|(ps, _, _)| ps)
            .unwrap_or_default()
    };
    // A `_refine` written on one *field* of a struct is an invariant of the
    // struct type just as a struct-level one is, and it means the same thing
    // wherever a value of that type is: `this` is the field. The generated
    // ownership cannot carry it -- it is built from representations and has no
    // hook for a clause -- so it is stated in the contract of every function
    // that holds such a struct, at whichever ends the struct itself is stated.
    let field_refines = |ty: &Type| -> Vec<(String, String, Rc<Type>, Rc<Expr>)> {
        let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(tds, ty).val else {
            return Vec::new();
        };
        let sname = n.val.to_string();
        let Some(si) = tds.structs.get(&sname) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for f in &si.fields {
            let Ok((ps, _, _)) = refinements(tds, &f.ty) else {
                continue;
            };
            for cl in ps {
                out.push((sname.clone(), f.name.clone(), f.ty.clone(), cl));
            }
        }
        out
    };
    // The `_own` predicate a value of this type carries, when its type is a
    // struct that has one.
    // `peel` and not `resolve`: the annotation that makes a struct interesting
    // is as often on the typedef that names it, and a `_refine` wrapper must
    // not hide the struct underneath.
    let own_for = |ty: &Type| -> Option<(String, String)> {
        let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(tds, ty).val else {
            return None;
        };
        tds.structs
            .get(&*n.val.to_string())
            .filter(|si| !own_items(tds, si, &n.val).is_empty())
            .map(|_| {
                (
                    format!("struct_{}", n.val),
                    format!("struct_{}_own_spec", n.val),
                )
            })
    };
    let mut refines: Vec<(String, Rc<Type>, Rc<Expr>)> = Vec::new();
    /// A refinement a *pointer* parameter inherits from the struct it points
    /// at. `this` is the pointee, so it is spelled with the pointee's value
    /// term rather than with the parameter.
    let mut refines_struct: Vec<(String, Rc<Type>, Rc<Expr>)> = Vec::new();
    /// A refinement written on one field of the struct a parameter is, or
    /// points at: the parameter, the field's name and type, the clause, and
    /// whether the struct is behind a pointer (so that `this` is the pointee's
    /// value) or is the parameter itself.
    let mut refines_field: Vec<(String, String, String, Rc<Type>, Rc<Expr>, bool)> = Vec::new();
    /// The parameters whose refinements sit behind a nullness guard, and the
    /// pointer the guard tests. `unless_null p (a ** b)` and
    /// `unless_null p a ** unless_null p b` are the same slprop, so a guarded
    /// refinement is an ordinary conjunct with the guard put back around it.
    let mut null_wrap: HashMap<String, String> = HashMap::new();
    // `_refine_uninit` clauses, kept apart because they are stated only where
    // the unwritten points-to is: on the way in, for an `_out` parameter.
    let mut refines_uninit: Vec<(String, Rc<Type>, Rc<Expr>)> = Vec::new();
    // A `_refine_value` on a parameter: the parameter it is written on, that
    // parameter's type, the name of the binder the contract quantifies over,
    // the F* type of that binder, and the clause itself.
    let mut refines_value: Vec<RefineValueOn> = Vec::new();
    // Parameters the caller hands over for good. Ownership stated at a
    // `_plain` parameter has no points-to to follow, so whether it comes back
    // has to be read off the mode directly.
    let mut consumed: HashSet<String> = HashSet::new();
    let mut refine_err: Option<String> = None;
    // Parameters whose ownership the contract puts behind `unless_null`.
    let mut guarded: HashSet<String> = HashSet::new();

    for (i, arg) in decl.args.iter().enumerate() {
        let pname = match &arg.name {
            Some(n) => format!("var_{}", n.val),
            None => format!("arg_{}", i),
        };
        let fty = fstar_type(tds, &arg.ty)
            .ok_or_else(|| format!("parameter {} is {}", pname, describe(tds.resolve(&arg.ty))))?;
        params.push(format!("({}: {})", pname, fty));

        // A user-supplied ownership predicate is a contract even when the
        // parameter is `_plain` and so has no points-to of its own -- `_plain`
        // is there precisely to make room for one. Checking before the
        // `pointee` early-out is what stops such a contract from being dropped
        // without a word, which is the failure mode that matters: a weaker
        // specification nothing downstream can see is weaker.
        if let Err(why) = refinements(tds, &arg.ty) {
            refine_err.get_or_insert(format!("parameter {} carries {}", pname, why));
        }
        // A `_refine_uninit` is a claim about storage the callee is handed
        // unwritten. Anywhere else there is no uninitialised points-to for it
        // to sit beside, so saying it would be saying it of nothing.
        if uninit_below_pointer(tds, &arg.ty) && !matches!(arg.mode, ParamMode::Out) {
            refine_err.get_or_insert(format!(
                "parameter {} carries a `_refine_uninit` but is not `_out`",
                pname
            ));
        }

        // A refinement on a parameter with no storage is still a refinement.
        // Collecting it here rather than only in the pointer branch below is
        // what stops it from vanishing: a `_refine` on a scalar is a claim
        // about the value, and one on a function pointer is a claim about the
        // code, and neither has a pointee to hang from.
        if matches!(arg.mode, ParamMode::Consumed) {
            consumed.insert(pname.trim_start_matches("var_").to_string());
        }
        if pointee(tds, &arg.ty).is_none()
            && let Ok((ps, _, bs)) = refinements(tds, &arg.ty)
        {
            let base = pname.trim_start_matches("var_").to_string();
            refines.extend(ps.into_iter().map(|p| (base.clone(), arg.ty.clone(), p)));
            refines.extend(
                struct_refines(&arg.ty)
                    .into_iter()
                    .map(|p| (base.clone(), arg.ty.clone(), p)),
            );
            refines_field.extend(
                field_refines(&arg.ty)
                    .into_iter()
                    .map(|(sn, f, fty, p)| (base.clone(), sn, f, fty, p, false)),
            );
            collect_valued(&mut refines_value, &mut refine_err, tds, &base, &arg.ty, bs);
        }

        let Some(pt) = pointee(tds, &arg.ty) else {
            // A struct passed by value still owns what its pointers reach.
            // The value is the parameter itself, so the deep half attaches
            // to it directly with no points-to to hang from -- which is the
            // clearest case for keeping the two predicates apart, since here
            // there is no first one at all.
            if let Some((sn, osty)) = own_for(&arg.ty) {
                let base = pname.trim_start_matches("var_").to_string();
                let oname = format!("own_{}", base);
                ghosts.push(format!("(#{}: erased ({}))", oname, osty));
                wits.push((oname.clone(), osty.clone(), true));
                req.push(format!("{}_own {} 1.0R (reveal {})", sn, pname, oname));
                fresh.push((
                    format!("{}'", oname),
                    osty,
                    format!("{}_own {} 1.0R {}'", sn, pname, oname),
                ));
                owns.insert(
                    pname.clone(),
                    (
                        Some(format!("(reveal {})", oname)),
                        Some(format!("{}'", oname)),
                    ),
                );
            }
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
        // A kind of refinement Palow cannot state is not a reason to drop the
        // function -- it is a reason to say its contract is incomplete, which
        // is what the dropped-contract path already does, and which is what
        // stops a caller from proving against the weaker version.
        match refinements(tds, &arg.ty) {
            Ok((ps, us, bs)) => {
                // A refinement found *below* the pointer is about the
                // pointee, however it was written -- on the struct, or on a
                // typedef that names it, or on the pointee type of the
                // parameter's own typedef. `this` is then the pointee, so it
                // belongs with the struct's own refinements and not with the
                // pointer's: bound as a value, it can be projected at a field
                // and asked what that field owns. Bound as the pointer it
                // would be an address, and a question about a field of an
                // address has no answer.
                let below = refinements(tds, pt)
                    .map(|(ps, _, _)| ps)
                    .unwrap_or_default();
                for cl in ps {
                    if below.iter().any(|q| Rc::ptr_eq(q, &cl)) {
                        refines_struct.push((base.clone(), pt.clone(), cl));
                    } else {
                        refines.push((base.clone(), arg.ty.clone(), cl));
                    }
                }
                // A struct's own refinement is about the struct, so `this`
                // is bound at the *pointee* type and to the pointee's value:
                // the declaration writes `this.x`, not `(*this).x`, and it
                // means the same thing whether the parameter holding it is a
                // value or an address.
                refines_struct.extend(
                    struct_refines(pt)
                        .into_iter()
                        .map(|p| (base.clone(), pt.clone(), p)),
                );
                refines_field.extend(
                    field_refines(pt)
                        .into_iter()
                        .map(|(sn, f, fty, p)| (base.clone(), sn, f, fty, p, true)),
                );
                refines_uninit.extend(us.into_iter().map(|p| (base.clone(), arg.ty.clone(), p)));
                // `_refine_always` means what it says: it holds of the storage
                // as much as of the value. For an `_out` array that is the
                // only thing the precondition can state -- the cells hold
                // nothing, but there are still as many of them as the
                // refinement says.
                if arg.mode == ParamMode::Out && extent(tds, &arg.ty) == Some(Extent::Array) {
                    refines_uninit.extend(
                        always_refines(tds, &arg.ty)
                            .into_iter()
                            .map(|p| (base.clone(), arg.ty.clone(), p)),
                    );
                }
                collect_valued(&mut refines_value, &mut refine_err, tds, &base, &arg.ty, bs);
            }
            Err(why) => {
                refine_err.get_or_insert(format!("parameter {} carries {}", pname, why));
            }
        }

        // `_nullable` says the pointer may be null, so the ownership is there
        // only when it is not: `unless_null p (...)`. The value binder stays --
        // it is erased, and when the pointer is null it is simply arbitrary,
        // which is how the guard is introduced in the first place.
        let null_guard = is_nullable(tds, &arg.ty);
        if null_guard {
            guarded.insert(base.clone());
        }

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
                    // `_out` says the callee is handed storage rather than a
                    // value, and storage is the `option` view: the length is
                    // fixed -- it is what the caller allocated -- but no
                    // element is promised to hold anything. Keeping the
                    // sequence as a binder rather than hiding it behind
                    // `array_pts_to_uninit` is what lets `a._length` go on
                    // meaning `Seq.length` of it.
                    if arg.mode == ParamMode::Out {
                        (
                            format!("Seq.seq (option ({}))", vty),
                            Box::new(move |perm: &str, v: &str| {
                                format!(
                                    "array_pts_to (maybe_repr {pn}_repr {esize}) {esize} {p} \
                                     {perm} {v}"
                                )
                            }),
                        )
                    } else {
                        (
                            format!("Seq.seq {}", vty),
                            Box::new(move |perm: &str, v: &str| {
                                format!("array_pts_to {}_repr {} {} {} {}", pn, esize, p, perm, v)
                            }),
                        )
                    }
                }
            };
        // The deep half of the parameter's ownership. A struct pointer in C
        // almost always means the struct *and* what its pointers reach; the
        // two are separate predicates here, so the contract states both. A
        // struct with no owned pointer field has nothing to add and gets
        // nothing, which is why this is an option rather than a conjunct.
        let own_info: Option<(String, String)> = (extent(tds, &arg.ty) == Some(Extent::One))
            .then(|| own_for(pt))
            .flatten();
        let oname = format!("own_{}", base);

        let pts_to: Box<dyn Fn(&str, &str) -> String> = if null_guard {
            let p = pname.clone();
            Box::new(move |perm: &str, v: &str| format!("unless_null {} ({})", p, pts_to(perm, v)))
        } else {
            pts_to
        };

        // A nullable parameter's pointee is behind the guard, so a contract
        // that mentions it -- or a body that reads it -- is talking about
        // something it does not unconditionally have. Leaving it out of the
        // pointee map is what makes those say so rather than quietly succeed
        // against a precondition the caller never granted.
        if null_guard {
            match refinements(tds, &arg.ty) {
                // Ownership survives the guard: it is stated where the
                // points-to is stated, inside it. A *proposition* does not --
                // it would have to become an implication rather than a
                // conjunct, and nothing yet writes one.
                Ok((ps, us, bs)) if us.is_empty() && bs.is_empty() => {
                    for cl in ps {
                        if slprop_refine(tds, &cl).is_none() {
                            refine_err.get_or_insert(format!(
                                "parameter {} carries a value refinement behind a nullness guard",
                                pname
                            ));
                            continue;
                        }
                        null_wrap.insert(base.clone(), pname.clone());
                        // A parameter with no pointee -- an `_arrayptr`, say --
                        // had its refinements collected above already.
                        if !refines
                            .iter()
                            .any(|(b, _, q)| *b == base && Rc::ptr_eq(q, &cl))
                        {
                            refines.push((base.clone(), arg.ty.clone(), cl));
                        }
                    }
                }
                _ => {
                    refine_err.get_or_insert(format!(
                        "parameter {} carries a refinement behind a nullness guard",
                        pname
                    ));
                }
            }
            match arg.mode {
                ParamMode::Out => return Err(format!("parameter {} is a nullable `_out`", pname)),
                ParamMode::Const => {
                    let perm = format!("perm_{}", base);
                    perms.push(format!("(#{}: perm)", perm));
                    wits.push((perm.clone(), "perm".to_string(), false));
                    ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                    wits.push((vname.clone(), vty.clone(), true));
                    preserved.push(pts_to(&perm, &vname));
                }
                ParamMode::Consumed => {
                    ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                    wits.push((vname.clone(), vty.clone(), true));
                    req.push(pts_to("1.0R", &vname));
                }
                ParamMode::Regular => {
                    ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                    wits.push((vname.clone(), vty.clone(), true));
                    req.push(pts_to("1.0R", &vname));
                    fresh.push((
                        format!("{}'", vname),
                        vty,
                        pts_to("1.0R", &format!("{}'", vname)),
                    ));
                }
            }
            continue;
        }

        match arg.mode {
            // `_out`: the callee is handed storage, not a value. This is the
            // one parameter mode the current model cannot express at all --
            // a `ref t` always holds a `t` -- and here it is just the
            // uninitialised points-to.
            ParamMode::Out if extent(tds, &arg.ty) == Some(Extent::One) => {
                req.push(format!("{}_pts_to_uninit {}", pn, pname));
                // The mode is a statement about the *pre*condition: what
                // arrives is storage. What leaves is the initialised object,
                // unless the author wrote an `_ensures` that states ownership
                // itself -- then the object has been handed somewhere, and
                // promising it back as well would be promising it twice.
                if !ens_own {
                    fresh.push((
                        format!("{}'", vname),
                        vty,
                        pts_to("1.0R", &format!("{}'", vname)),
                    ));
                }
                pointees.insert(base, (None, Some(format!("{}'", vname))));
            }
            // An `_out` array leaves fully initialised: that is the whole of
            // what the mode promises, and it is what every caller wants back.
            // The `option` view goes in, the plain one comes out, and the
            // length is the same storage either way.
            ParamMode::Out => {
                let esize = palow_sizeof(tds, pt).unwrap();
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                wits.push((vname.clone(), vty.clone(), true));
                req.push(pts_to("1.0R", &vname));
                let plain = fstar_type(tds, pt).unwrap();
                fresh.push((
                    format!("{}'", vname),
                    format!("Seq.seq {}", plain),
                    format!(
                        "array_pts_to {pn}_repr {esize} {pname} 1.0R {vname}' ** \
                         pure (Seq.length {vname}' == Seq.length (reveal {vname}))"
                    ),
                ));
                olens.insert(base.clone(), format!("(reveal {})", vname));
                pointees.insert(base, (None, Some(format!("{}'", vname))));
            }
            ParamMode::Const => {
                let perm = format!("perm_{}", base);
                perms.push(format!("(#{}: perm)", perm));
                wits.push((perm.clone(), "perm".to_string(), false));
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                wits.push((vname.clone(), vty.clone(), true));
                preserved.push(pts_to(&perm, &vname));
                owned.push(OwnedParam {
                    base: base.clone(),
                    vty: vty.clone(),
                    pre: pts_to(&perm, ""),
                    entry: format!("(reveal {})", vname),
                });
                if let Some((sn, osty)) = &own_info {
                    ghosts.push(format!("(#{}: erased ({}))", oname, osty));
                    wits.push((oname.clone(), osty.clone(), true));
                    preserved.push(format!(
                        "{}_own (reveal {}) {} (reveal {})",
                        sn, vname, perm, oname
                    ));
                    let o = format!("(reveal {})", oname);
                    owns.insert(format!("(reveal {})", vname), (Some(o.clone()), Some(o)));
                }
                let v = format!("(reveal {})", vname);
                pointees.insert(base, (Some(v.clone()), Some(v)));
            }
            ParamMode::Consumed => {
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                wits.push((vname.clone(), vty.clone(), true));
                req.push(pts_to("1.0R", &vname));
                owned.push(OwnedParam {
                    base: base.clone(),
                    vty: vty.clone(),
                    pre: pts_to("1.0R", ""),
                    entry: format!("(reveal {})", vname),
                });
                if let Some((sn, osty)) = &own_info {
                    ghosts.push(format!("(#{}: erased ({}))", oname, osty));
                    wits.push((oname.clone(), osty.clone(), true));
                    req.push(format!(
                        "{}_own (reveal {}) 1.0R (reveal {})",
                        sn, vname, oname
                    ));
                    owns.insert(
                        format!("(reveal {})", vname),
                        (Some(format!("(reveal {})", oname)), None),
                    );
                }
                pointees.insert(base, (Some(format!("(reveal {})", vname)), None));
            }
            ParamMode::Regular => {
                ghosts.push(format!("(#{}: erased ({}))", vname, vty));
                wits.push((vname.clone(), vty.clone(), true));
                req.push(pts_to("1.0R", &vname));
                owned.push(OwnedParam {
                    base: base.clone(),
                    vty: vty.clone(),
                    pre: pts_to("1.0R", ""),
                    entry: format!("(reveal {})", vname),
                });
                fresh.push((
                    format!("{}'", vname),
                    vty,
                    pts_to("1.0R", &format!("{}'", vname)),
                ));
                // The new value comes first, because what the deep half owns
                // is stated in terms of it: a body that overwrote a pointer
                // field owns what the *new* pointer reaches.
                if let Some((sn, osty)) = &own_info {
                    ghosts.push(format!("(#{}: erased ({}))", oname, osty));
                    wits.push((oname.clone(), osty.clone(), true));
                    req.push(format!(
                        "{}_own (reveal {}) 1.0R (reveal {})",
                        sn, vname, oname
                    ));
                    fresh.push((
                        format!("{}'", oname),
                        osty.clone(),
                        format!("{}_own {}' 1.0R {}'", sn, vname, oname),
                    ));
                    // The two ends have different value terms as well as
                    // different ownership records, so each spelling of the
                    // struct gets the record that goes with it.
                    owns.insert(
                        format!("(reveal {})", vname),
                        (Some(format!("(reveal {})", oname)), None),
                    );
                    owns.insert(format!("{}'", vname), (None, Some(format!("{}'", oname))));
                }
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

    // A `_ghost_arg` is a value the caller supplies purely so that the
    // contract can talk about it: it has no representation, no storage and no
    // runtime existence. An erased implicit is exactly that, and the model has
    // nothing to add.
    for ga in &decl.ghost_args {
        let vty = fstar_type(tds, &ga.ty).ok_or_else(|| {
            format!(
                "ghost argument {} is {}",
                ga.name.val,
                describe(tds.resolve(&ga.ty))
            )
        })?;
        ghosts.push(format!("(#var_{}: erased ({}))", ga.name.val, vty));
        wits.push((format!("var_{}", ga.name.val), vty.clone(), true));
    }

    // A mutable global's storage outlives every function, so C gives no
    // syntax for who owns it. The caller does: the ownership comes in as a
    // conjunct the source never wrote and goes straight back out, at a value
    // the body may have changed. That is the awkward part -- `main` has no
    // caller to get it from -- and the reason it is still the right shape is
    // that it can say what a global's life actually looks like: uninitialised,
    // then written by one thread during start-up, then shared read-only.
    for g in globals {
        ghosts.push(format!("(#gval_{}: erased ({}))", g.name, g.fstar_ty));
        req.push(g.pts_to(&format!("gval_{}", g.name)));
        fresh.push((
            format!("gval_{}'", g.name),
            g.fstar_ty.clone(),
            g.pts_to(&format!("gval_{}'", g.name)),
        ));
        // Having named the value the ownership is at, the contract can talk
        // about it: `g` in a specification is that value, before and after,
        // exactly as a pointer parameter's pointee is. The global is not
        // reached through a pointer, but nothing in the translation of `*p` or
        // `p[i]` depended on that -- what it needs is a term for the contents,
        // and the conjunct that hands the ownership over supplies one.
        pointees.insert(
            g.name.clone(),
            (
                Some(format!("(reveal gval_{})", g.name)),
                Some(format!("gval_{}'", g.name)),
            ),
        );
        if g.array.is_some() {
            arrays.insert(g.name.clone());
        }
    }

    let ret = fstar_type(tds, &decl.ret_type)
        .ok_or_else(|| format!("it returns {}", describe(tds.resolve(&decl.ret_type))))?;
    let ret_name = format!("ret_{}", decl.name.val);

    // `_allocated` on a *return* type is the only way C has of saying that a
    // function hands its caller a block: storage the caller now owns, may read
    // and write, and must eventually free. Until now the postcondition simply
    // left that out, which made every allocating constructor look like it
    // returned a bare address -- a caller could not read through the pointer,
    // could not free it, and, worst of all, nothing said so. The block goes
    // into the `ensures` the same way a parameter's ownership does: an
    // existential for the value it holds, the points-to at full permission,
    // and the `freeable` the annotation asked for.
    let mut ret_freeable: Option<String> = None;
    // The same grant when the return type is `_nullable`: one conjunct, with
    // everything the block gives inside the guard.
    // The pieces of that guard: the binders it quantifies and the conjuncts it
    // encloses so far. It is assembled only once the author's own `ensures`
    // have been translated, because a clause about what the block holds has to
    // go *inside* -- there is nothing for it to be about when the allocation
    // failed, and stating it outside would be a promise the callee cannot
    // keep.
    let mut ret_guard: Option<(String, String, Vec<String>)> = None;
    let mut ret_block: Option<RetBlock> = None;
    // Ownership the author wrote on the return type in their own Pulse, which
    // `_allocated` is only the commonest case of. A constructor that hands back
    // a validated object says so with a `_refine` or a `_refine_value` on the
    // returned pointer, and the contract has to carry it for the same reason:
    // otherwise the caller is handed an address and nothing else.
    let mut ret_slprops: Vec<Rc<Expr>> = Vec::new();
    let mut ret_valued: Vec<RefineValueOn> = Vec::new();
    if let Ok((ps, _, bs)) = refinements(tds, &decl.ret_type) {
        let alloc = ps.iter().find_map(|p| {
            let code = slprop_refine(tds, p)?;
            allocated_own(tds, &decl.ret_type, &ret_name, code)
                .ok()
                .flatten()
        });
        ret_slprops.extend(
            ps.iter()
                .filter(|p| {
                    slprop_refine(tds, p).is_some()
                        && allocated_own(
                            tds,
                            &decl.ret_type,
                            &ret_name,
                            slprop_refine(tds, p).unwrap(),
                        )
                        .ok()
                        .flatten()
                        .is_none()
                })
                .cloned(),
        );
        collect_valued(
            &mut ret_valued,
            &mut refine_err,
            tds,
            "return",
            &decl.ret_type,
            bs,
        );
        if let Some(freeable) = alloc {
            let pt = pointee(tds, &decl.ret_type).unwrap();
            match (
                palow_name(tds, pt),
                fstar_type(tds, pt),
                extent(tds, &decl.ret_type),
            ) {
                // `_nullable` says the allocation may have failed, and that
                // is the honest contract for a constructor: a caller that
                // tests the result gets the block, and one that does not gets
                // nothing it can use. The guard has to enclose the value
                // binder as well as the ownership -- there is no value when
                // there is no object -- so this conjunct is built whole rather
                // than through `fresh`, and the pointee map deliberately stays
                // empty, which is what makes a contract that dereferences the
                // result say so.
                (Some(pn), Some(vty), Some(Extent::One)) if is_nullable(tds, &decl.ret_type) => {
                    let mut binders = format!("(val_return: {})", vty);
                    let mut inner = vec![
                        format!("{}_pts_to {} 1.0R val_return", pn, PTR_HOLE),
                        freeable.replace(&ret_name, PTR_HOLE),
                    ];
                    if let Some((sn, osty)) = own_for(pt) {
                        binders += &format!(" (own_return: {})", osty);
                        inner.push(format!("{}_own val_return 1.0R own_return", sn));
                        owns.insert(
                            "val_return".to_string(),
                            (None, Some("own_return".to_string())),
                        );
                    }
                    pointees.insert("return".to_string(), (None, Some("val_return".to_string())));
                    refines_struct.extend(
                        struct_refines(pt)
                            .into_iter()
                            .map(|p| ("return".to_string(), pt.clone(), p)),
                    );
                    refines_field.extend(
                        field_refines(pt)
                            .into_iter()
                            .map(|(sn, f, fty, p)| ("return".to_string(), sn, f, fty, p, true)),
                    );
                    ret_guard = Some((pn, binders, inner));
                }
                (Some(pn), Some(vty), Some(Extent::One)) => {
                    fresh.push((
                        "val_return".to_string(),
                        vty,
                        format!("{}_pts_to {} 1.0R val_return", pn, ret_name),
                    ));
                    ret_freeable = Some(freeable);
                    // A returned struct pointer owns what its own pointers
                    // reach, exactly as a parameter does; the deep half is
                    // stated at the value the existential just named.
                    if let Some((sn, osty)) = own_for(pt) {
                        fresh.push((
                            "own_return".to_string(),
                            osty,
                            format!("{}_own val_return 1.0R own_return", sn),
                        ));
                        owns.insert(
                            "val_return".to_string(),
                            (None, Some("own_return".to_string())),
                        );
                    }
                    // Having named the value, the contract can talk about it:
                    // `*return` and `return->f` resolve through the pointee
                    // map like any parameter's dereference, and the pointee
                    // type's own refinements have somewhere to be stated.
                    pointees.insert("return".to_string(), (None, Some("val_return".to_string())));
                    ret_block = Some(RetBlock { pn, guarded: None });
                    refines_struct.extend(
                        struct_refines(pt)
                            .into_iter()
                            .map(|p| ("return".to_string(), pt.clone(), p)),
                    );
                    refines_field.extend(
                        field_refines(pt)
                            .into_iter()
                            .map(|(sn, f, fty, p)| ("return".to_string(), sn, f, fty, p, true)),
                    );
                }
                _ => {
                    refine_err.get_or_insert(match pointee(tds, &decl.ret_type) {
                        Some(pt) => format!(
                            "an `_allocated` return of a pointer to {}",
                            describe(tds.resolve(pt))
                        ),
                        None => {
                            "an `_allocated` return of something that is not a pointer".to_string()
                        }
                    });
                }
            }
        }
    }

    // The contract is all-or-nothing: a half-translated one would be silently
    // weaker in a way nothing downstream could detect.
    let spec = Spec {
        tds,
        env,
        pointees,
        olds: HashMap::new(),
        arrays,
        olens: olens.clone(),
        owns,
        addrs: HashMap::new(),
        guarded: guarded.clone(),
        guards: RefCell::new(Vec::new()),
        ret: ret_name.clone(),
        locals: HashMap::new(),
        uses: RefCell::new(HashSet::new()),
        signed_ok: false,
        valued: RefCell::new(Vec::new()),
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
    // A `_refine` is stated wherever the parameter's points-to is, and the
    // pointee map already records exactly that: an entry term where the caller
    // supplies ownership, an exit term where the callee hands it back. So the
    // clause is translated against `this` bound to that same parameter -- no
    // substitution needed, because the contract machinery resolves `*this`
    // through the map like any other dereference.
    // Translate something written in terms of `$(this)` against one parameter.
    // The caller says what to do with the specification translator once `this`
    // is bound, because the two things a refinement can be -- a proposition and
    // a piece of ownership -- take different routes out of it.
    // `as_value` forces the second reading below. A `_refine_uninit` needs it:
    // the storage it talks about has no value, so `$(this)` can only mean the
    // pointer itself, even for a parameter that does have a pointee entry.
    // `bind` is what a `_refine_value` adds: besides `$(this)` the clause may
    // name the value the contract quantifies over, and that name is spelled
    // differently at the two ends of the contract, so the caller supplies it.
    // `this_value` overrides what `this` *is*: the term for the pointee's
    // value rather than the parameter. A refinement written on a struct
    // declaration needs it -- the declaration says `this.x`, meaning the
    // struct, and that is the pointee when the parameter is a pointer to one.
    // Its third component says the override is only about the *spelling*: the
    // clause still reads `*this` through the pointee entry `base` has. That is
    // what a refinement on a *return* type needs -- `this` is the returned
    // pointer, which is spelled with the result binder rather than
    // `var_return`, but a clause about what it points at is still a clause
    // about the value the `ensures` grants.
    // `siblings` are the other fields of the struct a *field* refinement is
    // written on, as (C name, term, type). A clause written on a field names
    // its siblings without any qualification -- `_refines(this._length == len)`
    // is the whole point of a flexible array member -- so they have to be in
    // scope both as terms and as types, and there is no function whose
    // environment could have put them there.
    let with_this = |base: &str,
                     this_value: Option<(&str, Option<&str>, bool)>,
                     ty: &Rc<Type>,
                     p: &Rc<Expr>,
                     w: When,
                     as_value: bool,
                     bind: Option<(&Rc<Ident>, String, &Rc<Type>)>,
                     siblings: &[(String, String, Rc<Type>)],
                     how: &dyn Fn(&Spec, When) -> Result<String, String>|
     -> Result<String, String> {
        let mut pointees = spec.pointees.clone();
        let mut arrays = spec.arrays.clone();
        let mut olens = spec.olens.clone();
        let mut locals = HashMap::new();
        // A refinement read against the *storage* rather than the value --
        // which is the only reading an `_out` parameter has on the way in --
        // can still ask how much storage there is. `this._length` is then the
        // length of the cells the caller handed over.
        if as_value && let Some(t) = olens.get(base).cloned() {
            olens.insert("this".to_string(), t);
            arrays.insert("this".to_string());
        }
        if let Some((n, spelling, _)) = &bind {
            locals.insert(n.val.to_string(), spelling.clone());
        }
        // `$(this)` means the parameter. Which parameter it is decides what
        // that means: for a pointer it is the storage the contract grants,
        // so `this` inherits the pointee entry and `$(this)` reads through
        // it; for anything else -- a scalar, a function pointer -- there is
        // no storage and `this` is simply the value, so it is bound as a
        // local instead. Without the second case a `_refine` on such a
        // parameter had nowhere to go and was dropped in silence.
        let by_value = match pointees
            .get(base)
            .cloned()
            .filter(|_| !as_value && matches!(this_value, None | Some((_, _, true))))
        {
            Some(entry) => {
                pointees.insert("this".to_string(), entry);
                if arrays.contains(base) {
                    arrays.insert("this".to_string());
                }
                // `*this` reads through the entry; bare `$(this)` is still the
                // pointer itself, and without this it would come out as the
                // name of a binder nobody declared.
                locals.insert(
                    "this".to_string(),
                    this_value
                        .map(|(v, _, _)| v.to_string())
                        .unwrap_or_else(|| format!("var_{}", base)),
                );
                false
            }
            None => {
                locals.insert(
                    "this".to_string(),
                    this_value
                        .map(|(v, _, _)| v.to_string())
                        .unwrap_or_else(|| format!("var_{}", base)),
                );
                // A `this` bound to a *field* is the field's value, which for
                // an array field is an address and not the sequence behind it.
                // `this._length` asks about the sequence, and the sequence is
                // in the struct's ownership record, so the caller hands it
                // over here: without it the only refinement anyone writes on
                // an array field -- its length -- could not be stated.
                if let Some((_, Some(pt), _)) = this_value {
                    pointees.insert(
                        "this".to_string(),
                        (Some(pt.to_string()), Some(pt.to_string())),
                    );
                    arrays.insert("this".to_string());
                }
                true
            }
        };
        // The clause is never elaborated -- `this` is free in it, so nothing
        // could have typed it -- and the specification translator asks for
        // types. Binding `this` to the parameter's own type is what makes the
        // clause typeable, and is also exactly what it means.
        let mut env = env.clone();
        // A by-value `this` is bound at the *peeled* type. Leaving the
        // refinement on would make the binder's type the very thing being
        // refined, and everything that asks what kind of integer `this` is --
        // an overflow bound, a `_specint` cast -- would stop at the refinement
        // and find no answer.
        env.push_var_decl(
            &Rc::<str>::from("this").with_loc(p.loc.clone()),
            if by_value {
                Rc::new(peel(tds, ty).clone())
            } else {
                ty.clone()
            },
            if by_value {
                crate::env::LocalDeclKind::RValue
            } else {
                crate::env::LocalDeclKind::LValue
            },
        );
        if let Some((n, _, vty)) = &bind {
            env.push_var_decl(n, (*vty).clone(), crate::env::LocalDeclKind::RValue);
        }
        for (n, term, sty) in siblings {
            env.push_var_decl(
                &Rc::<str>::from(n.as_str()).with_loc(p.loc.clone()),
                sty.clone(),
                crate::env::LocalDeclKind::RValue,
            );
            locals.insert(n.clone(), term.clone());
        }
        let inner = Spec {
            tds,
            env: &env,
            pointees,
            olds: spec.olds.clone(),
            arrays,
            olens,
            owns: spec.owns.clone(),
            addrs: spec.addrs.clone(),
            guarded: spec.guarded.clone(),
            guards: RefCell::new(Vec::new()),
            ret: ret_name.clone(),
            locals,
            uses: RefCell::new(HashSet::new()),
            signed_ok: false,
            valued: RefCell::new(Vec::new()),
        };
        let r = how(&inner, w);
        spec.uses
            .borrow_mut()
            .extend(inner.uses.borrow().iter().cloned());
        r
    };
    let refine_clause = |base: &str,
                         this_value: Option<(&str, Option<&str>, bool)>,
                         ty: &Rc<Type>,
                         p: &Rc<Expr>,
                         w: When,
                         as_value: bool,
                         siblings: &[(String, String, Rc<Type>)]| {
        with_this(
            base,
            this_value,
            ty,
            p,
            w,
            as_value,
            None,
            siblings,
            &|sp: &Spec, w| sp.prop(p, w),
        )
    };
    // Whether a parameter's ownership is stated at this end of the contract,
    // which is also where its refinements belong.
    // A parameter that owns nothing is a value, and a value parameter is
    // immutable, so its refinement is a precondition and nothing more: stating
    // it again on the way out would add nothing the caller could not already
    // derive.
    let stated = |base: &str, w: When| match spec.pointees.get(base) {
        None => matches!(w, When::Pre),
        Some((pre, post)) => match w {
            When::Post => post.is_some(),
            _ => pre.is_some(),
        },
    };
    // The term `this` stands for in a field refinement: the struct's value
    // projected at the field. Which struct value that is depends on whether the
    // parameter is the struct or points at it, and it exists only at the ends
    // of the contract where the struct's own ownership is stated.
    let field_this = |base: &str,
                      sname: &str,
                      fname: &str,
                      fty: &Rc<Type>,
                      via: bool,
                      w: When|
     -> Option<(String, Option<String>, Vec<(String, String, Rc<Type>)>)> {
        let this = if via {
            let (pre, post) = spec.pointees.get(base)?;
            match w {
                When::Post => post.clone()?,
                _ => pre.clone()?,
            }
        } else {
            if !stated(base, w) {
                return None;
            }
            format!("var_{}", base)
        };
        // A flexible array member is the one array field whose value is the
        // sequence itself, because there is nothing else it could be: the
        // elements are inside the object and their number is not in the type.
        // So `this` and the sequence behind it are the same term, which is
        // what makes `this._length == len` sayable at all.
        let own = if flex_elem(tds, fty).is_some() {
            Some(format!("({}).fld_{}", this, fname))
        } else if matches!(extent(tds, fty), Some(Extent::Array)) {
            spec.owns.get(&this).and_then(|(pre, post)| {
                let o = match w {
                    When::Post => post.as_deref(),
                    _ => pre.as_deref(),
                }?;
                Some(format!("({}).own_{}", o, fname))
            })
        } else {
            None
        };
        let siblings = tds
            .structs
            .get(sname)
            .map(|si| {
                si.fields
                    .iter()
                    .filter(|g| g.name != fname)
                    .map(|g| {
                        (
                            g.name.clone(),
                            format!("(({}).fld_{})", this, g.name),
                            g.ty.clone(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        Some((format!("({}).fld_{}", this, fname), own, siblings))
    };
    let refine_props = |w: When| -> Result<Vec<String>, String> {
        if let Some(why) = &refine_err {
            return Err(why.clone());
        }
        let mut out = Vec::new();
        for (base, ty, p) in &refines {
            if slprop_refine(tds, p).is_some() {
                continue;
            }
            if stated(base, w) {
                out.push(refine_clause(base, None, ty, p, w, false, &[])?);
            }
        }
        for (base, ty, p) in &refines_struct {
            let Some((pre, post)) = spec.pointees.get(base) else {
                continue;
            };
            let this = match w {
                When::Post => post.as_deref(),
                _ => pre.as_deref(),
            };
            if let Some(this) = this {
                out.push(refine_clause(
                    base,
                    Some((this, None, false)),
                    ty,
                    p,
                    w,
                    false,
                    &[],
                )?);
            }
        }
        for (base, sname, fname, fty, p, via) in &refines_field {
            if slprop_refine(tds, p).is_some() {
                continue;
            }
            if let Some((this, own, sibs)) = field_this(base, sname, fname, fty, *via, w) {
                out.push(refine_clause(
                    base,
                    Some((&this, own.as_deref(), false)),
                    fty,
                    p,
                    w,
                    false,
                    &sibs,
                )?);
            }
        }
        // An `_out` parameter's storage is unwritten exactly on the way in,
        // and that is the only place a `_refine_uninit` says anything. On the
        // way out the storage holds a value, so the clause is not merely
        // unnecessary there -- it is about a points-to that is gone.
        if matches!(w, When::Pre) {
            for (base, ty, p) in &refines_uninit {
                out.push(refine_clause(base, None, ty, p, w, true, &[])?);
            }
        }
        Ok(out)
    };
    // A refinement whose predicate is an `_slprop` is ownership the parameter
    // carries, not a fact about its value: `_allocated` is the one PAL itself
    // writes, and it says the caller hands over the right to free the block.
    // It goes where the points-to goes.
    let valid_fps: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
    // Whether a type-level `_refine` contributed ownership in the author's own
    // Pulse. Like a spliced contract clause, it can grant something the
    // emitter never reads, so the body has to stop insisting it knows what is
    // unowned.
    let refine_own_spliced: RefCell<bool> = RefCell::new(false);
    // The same, for a function pointer held in a *field* of a struct the
    // contract owns: the validity is stated at `x.fld_f`, so what the body may
    // call through is the field, not the parameter.
    let valid_fp_fields: RefCell<HashSet<(String, String)>> = RefCell::new(HashSet::new());
    let freeables: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
    let refine_own = |w: When| -> Result<Vec<String>, String> {
        let mut out = Vec::new();
        for (base, ty, p) in &refines {
            let Some(code) = slprop_refine(tds, p) else {
                continue;
            };
            // Ownership a parameter with no storage carries is stated at both
            // ends. A pure refinement need not be -- it is derivable from the
            // precondition -- but a resource is not a fact: handing it in and
            // never handing it back would leave the body holding something it
            // has no way to put down, and a body that calls through the
            // pointer twice needs it for the second call as much as the first.
            let both = spec.pointees.get(base).is_none() && !consumed.contains(base);
            if !both && !stated(base, w) {
                continue;
            }
            // `_allocated` is the one ownership refinement PAL writes itself,
            // and the model reads it natively. Anything else is the author's
            // own Pulse -- a function pointer's `is_valid`, say -- so it is
            // spliced under the same rule as an `_inline_pulse` contract
            // clause, and refused with the same words when that rule says no.
            let stated_own = match allocated_own(tds, ty, &format!("var_{}", base), code)? {
                Some(t) => {
                    // Only if the caller is giving it up: freeing what the
                    // `ensures` still promises back would be a body that
                    // cannot be proved.
                    if consumed.contains(base)
                        && let Some(pt) = pointee(tds, ty)
                        && let Some(pn) = palow_name(tds, &pt)
                    {
                        freeables.borrow_mut().insert(base.clone(), pn);
                    }
                    t
                }
                None => {
                    let t = with_this(base, None, ty, p, w, false, None, &[], &|sp: &Spec, w| {
                        sp.inline_pulse(code, w)
                    })?;
                    // A spliced ownership refinement on a function pointer
                    // is taken at its word: nothing else could be granting
                    // the validity an indirect call needs.
                    if matches!(peel(tds, ty).val, TypeT::FnPtr { .. }) {
                        valid_fps.borrow_mut().insert(base.clone());
                    }
                    *refine_own_spliced.borrow_mut() = true;
                    t
                }
            };
            out.push(match null_wrap.get(base) {
                Some(p) => format!("unless_null {} ({})", p, stated_own),
                None => stated_own,
            });
        }
        for (base, sname, fname, fty, p, via) in &refines_field {
            let Some(code) = slprop_refine(tds, p) else {
                continue;
            };
            let Some((this, own, sibs)) = field_this(base, sname, fname, fty, *via, w) else {
                continue;
            };
            out.push(with_this(
                base,
                Some((&this, own.as_deref(), false)),
                fty,
                p,
                w,
                false,
                None,
                &sibs,
                &|sp: &Spec, w| sp.inline_pulse(code, w),
            )?);
            if matches!(peel(tds, fty).val, TypeT::FnPtr { .. }) {
                valid_fp_fields
                    .borrow_mut()
                    .insert((base.clone(), fname.clone()));
            }
            *refine_own_spliced.borrow_mut() = true;
        }
        Ok(out)
    };
    // An `_inline_pulse` clause whose type is `_slprop` is ownership, not a
    // proposition: it belongs beside the generated points-to in `requires` and
    // `ensures`, not under a `pure`. Everything else stays a prop, so the two
    // are separated before translation rather than after.
    // A call to an slprop-valued `_let` is the same thing under a name: the
    // author has given a piece of ownership a word, and a contract that uses
    // the word means the ownership.
    let is_slprop = |e: &Rc<Expr>| is_slprop_clause(tds, e);
    let split = |es: &Exprs| -> (Exprs, Exprs) { es.iter().cloned().partition(|e| is_slprop(e)) };
    let (req_slprops, req_props) = split(&decl.requires);
    let (ens_slprops, ens_props) = split(&decl.ensures);
    let mut slprop_err: Option<String> = None;
    let generated_req = req.len();
    for (es, w, into) in [
        (&req_slprops, When::Pre, &mut req),
        (&ens_slprops, When::Post, &mut owned_post),
    ] {
        for e in es {
            let r = match &strip_vattr(e).val {
                ExprT::InlinePulse(code, _) => spec.inline_pulse(code, w),
                _ => spec.value(e, w),
            };
            match r {
                Ok(t) => into.push(t),
                Err(why) => {
                    slprop_err.get_or_insert(why);
                }
            }
        }
    }

    // `_refine_value` is a refinement that quantifies. The value it binds is
    // not the parameter's and not the pointee's -- it is whatever the author's
    // predicate says it is -- so it becomes an erased implicit on the way in
    // and a fresh existential on the way out, exactly like a pointee value.
    // What the clause then *is* follows the same split as every other
    // refinement: an `_slprop` is ownership and stands beside the points-to,
    // anything else is a proposition and goes under a `pure`.
    let mut value_req: Vec<String> = Vec::new();
    let mut value_fresh: Vec<(String, String, String)> = Vec::new();
    let mut value_err: Option<String> = None;
    for (base, ty, ident, vty, binder, fty, p) in &refines_value {
        let both = spec.pointees.get(base).is_none() && !consumed.contains(base);
        let wrap = |t: String| t;
        let how = |sp: &Spec, w: When| sp.refinement(p, w);
        match with_this(
            base,
            None,
            ty,
            p,
            When::Pre,
            false,
            Some((ident, format!("(reveal {})", binder), vty)),
            &[],
            &how,
        ) {
            Ok(t) => {
                ghosts.push(format!("(#{}: erased ({}))", binder, fty));
                value_req.push(wrap(t));
                spec.valued
                    .borrow_mut()
                    .push((base.clone(), fty.clone(), binder.clone(), false));
                // A spliced ownership refinement quantified over the value at
                // a pointer is taken at its word in the same way one written
                // on a function pointer is. What it is usually for is a
                // dispatch table: the struct's fields include code pointers,
                // and nothing but the author's own clause can say what the
                // code at them does.
                if refine_states_own(tds, p) {
                    valid_fps.borrow_mut().insert(base.clone());
                    // And it is ownership the emitter cannot read, which is
                    // what `spliced_own` is for: the body may reach things
                    // this clause grants and nothing generated does.
                    *refine_own_spliced.borrow_mut() = true;
                }
            }
            Err(why) => {
                value_err.get_or_insert(why);
                continue;
            }
        }
        if !(both || stated(base, When::Post)) {
            continue;
        }
        match with_this(
            base,
            None,
            ty,
            p,
            When::Post,
            false,
            Some((ident, format!("{}'", binder), vty)),
            &[],
            &how,
        ) {
            Ok(t) => {
                value_fresh.push((format!("{}'", binder), fty.clone(), wrap(t)));
                if let Some(e) = spec
                    .valued
                    .borrow_mut()
                    .iter_mut()
                    .find(|(b, _, bi, _)| b == base && bi == binder)
                {
                    e.3 = true;
                }
            }
            Err(why) => {
                value_err.get_or_insert(why);
            }
        }
    }

    // The return type's own refinements, stated where the result is: at the
    // exit end only, because there is no result before the call. `this` is the
    // returned value itself rather than a pointee -- a refinement written on a
    // pointer type is about the pointer -- so it is bound by value, and a
    // `_refine_value`'s binder becomes one more existential in the `ensures`.
    // These are the emitter's reading of an annotation rather than the
    // author's own clauses, so they survive a dropped contract: a caller that
    // cannot be told what the result satisfies can still be told what it owns.
    let mut ret_own: Vec<String> = Vec::new();
    let mut ret_fresh: Vec<(String, String, String)> = Vec::new();
    for p in &ret_slprops {
        let code = slprop_refine(tds, p).unwrap();
        match with_this(
            "return",
            Some((&ret_name, None, true)),
            &decl.ret_type,
            p,
            When::Post,
            false,
            None,
            &[],
            &|sp: &Spec, w| sp.inline_pulse(code, w),
        ) {
            Ok(t) => ret_own.push(t),
            Err(why) => {
                value_err.get_or_insert(why);
            }
        }
    }
    for (_, ty, ident, vty, binder, fty, p) in &ret_valued {
        let how = |sp: &Spec, w: When| sp.refinement(p, w);
        match with_this(
            "return",
            Some((&ret_name, None, true)),
            ty,
            p,
            When::Post,
            false,
            Some((ident, binder.clone(), vty)),
            &[],
            &how,
        ) {
            Ok(t) => {
                // The binder is also what a `_letimpure` accessor applied to
                // the result denotes, exactly as it is for a parameter: the
                // author named the ghost state once, and `_ensures` clauses
                // about the returned handle are written in terms of it.
                spec.valued.borrow_mut().push((
                    "return".to_string(),
                    fty.clone(),
                    binder.clone(),
                    true,
                ));
                ret_fresh.push((binder.clone(), fty.clone(), t))
            }
            Err(why) => {
                value_err.get_or_insert(why);
            }
        }
    }

    let mut own_pre: Vec<String> = Vec::new();
    let mut own_post: Vec<String> = Vec::new();
    let contract = translate(&req_props, When::Pre)
        .and_then(|pre| translate(&ens_props, When::Post).map(|post| (pre, post)))
        .and_then(|(mut pre, mut post)| {
            pre.extend(refine_props(When::Pre)?);
            post.extend(refine_props(When::Post)?);
            own_pre = refine_own(When::Pre)?;
            own_post = refine_own(When::Post)?;
            Ok((pre, post))
        });
    let (pre_props, post_props, contract_ok, dropped) = match contract {
        Ok((pre, post)) if slprop_err.is_none() && value_err.is_none() => {
            req.extend(own_pre.iter().cloned());
            req.extend(value_req.iter().cloned());
            owned_post.extend(own_post.iter().cloned());
            fresh.extend(value_fresh.iter().cloned());
            (pre, post, true, None)
        }
        contract => {
            // A half-translated contract is worse than none: the parts that
            // did translate would look like the whole thing. So a failure
            // anywhere drops all of it, including the hand-written ownership
            // gathered above.
            req.truncate(generated_req);
            owned_post.clear();
            let why = match contract {
                Err(why) => why,
                _ => slprop_err.or(value_err).unwrap_or_default(),
            };
            (
                Vec::new(),
                Vec::new(),
                decl.requires.is_empty() && decl.ensures.is_empty(),
                Some(why),
            )
        }
    };

    // The returned block is the emitter's own conjunct, not the author's, so
    // it survives a dropped contract: a caller that cannot be told what the
    // block holds can still be told that it has one.
    if let Some(f) = ret_freeable {
        owned_post.push(f);
    }
    fresh.extend(ret_fresh);
    owned_post.extend(ret_own);
    // `_allocated` is the commonest reason a returned pointer carries
    // something, but it is not the only one: a constructor may hand back a
    // validated object through a `_refine_value` instead. `_nullable` means
    // the same thing either way, so a return type that has no `_allocated`
    // still opens a guard for whatever the contract turns out to say.
    if ret_guard.is_none()
        && is_nullable(tds, &decl.ret_type)
        && let TypeT::Pointer(pt, _) = &peel(tds, &decl.ret_type).val
        && let Some(pn) = palow_name(tds, pt)
    {
        ret_guard = Some((pn, String::new(), Vec::new()));
    }
    // Everything the contract said about what the block holds belongs inside
    // the nullness guard, and nowhere else: the binders it speaks of are the
    // guard's, and the promise itself is conditional on there being an object
    // to make it about. Which clauses those are is read off the binders they
    // name, which is the only thing that decides it.
    let mut post_props = post_props;
    if let Some((pn, mut binders, mut inner)) = ret_guard {
        let about_block =
            |t: &str| t.contains("val_return") || t.contains("own_return") || t.contains(&ret_name);
        // An existential the contract opened for what the block holds is the
        // guard's to quantify: outside it there is no object for the binder to
        // range over.
        let (mine, rest): (Vec<_>, Vec<_>) = fresh
            .into_iter()
            .partition(|(b, _, t): &(String, String, String)| about_block(b) || about_block(t));
        fresh = rest;
        for (b, ty, t) in mine {
            binders += &format!(
                "{}({}: {})",
                if binders.is_empty() { "" } else { " " },
                b,
                ty
            );
            inner.push(t);
        }
        let (mine, rest): (Vec<String>, Vec<String>) =
            owned_post.into_iter().partition(|t| about_block(t));
        owned_post = rest;
        inner.extend(mine);
        let (mine, rest): (Vec<String>, Vec<String>) =
            post_props.into_iter().partition(|t| about_block(t));
        post_props = rest;
        inner.extend(mine.into_iter().map(|t| format!("pure ({})", t)));
        // A `_nullable` that guards nothing is just a pointer, and an empty
        // `exists*` is not a slprop, so say nothing rather than nothing at
        // length.
        if !inner.is_empty() {
            // The same words serve the caller, which has to name this slprop
            // to get past its own nullness test, so the pointer is left as a
            // hole rather than written twice.
            let body = inner.join(" ** ");
            let guard = if binders.is_empty() {
                format!("({})", body)
            } else {
                format!("(exists* {}. {})", binders, body)
            }
            .replace(&ret_name, PTR_HOLE);
            owned_post.push(format!(
                "unless_null {} {}",
                ret_name,
                guard.replace(PTR_HOLE, &ret_name)
            ));
            ret_block = Some(RetBlock {
                pn,
                guarded: Some(guard),
            });
        }
    }

    let mut out = String::new();
    if let Some(why) = dropped {
        // Silently weakening a contract would be undetectable downstream, so
        // say so in the generated file.
        out += &format!("(* contract dropped: {} *)\n", why);
    }
    // `_rec` with a `_decreases` is a total recursive function, and Pulse
    // spells one `fn rec ... decreases (...)`. Without a measure there is
    // nothing to prove termination with, and C supplies none, so the call is
    // refused in the body instead -- the same treatment a cycle through two
    // functions gets.
    let decreases = match (decl.is_rec, &decl.decreases) {
        (true, Some(d)) => {
            spec.guards.borrow_mut().clear();
            match spec.num(d, When::Pre) {
                Ok(t) if spec.guards.borrow().is_empty() && contract_ok => Some(t),
                _ => None,
            }
        }
        _ => None,
    };
    out += &format!(
        "fn {}{}",
        if decreases.is_some() { "rec " } else { "" },
        name
    );
    if params.is_empty() {
        // Pulse has no nullary `fn`; `f(void)` becomes `f ()`. A function whose
        // only binders are ghost still needs it, which a global grant can
        // produce.
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
    // Whether the precondition says anything at all beyond ownership. A bounds
    // or overflow obligation in the body is discharged by these, and it does
    // not matter whether the author wrote them as a `_requires` or the
    // emitter read them off a `_refine` on a parameter's type.
    let req_props = !pre_props.is_empty();
    req.extend(pre_props.iter().map(|p| format!("pure ({})", p)));
    if req.is_empty() {
        out += "  requires emp\n";
    } else {
        // One `requires` per clause rather than one `requires` joining them
        // with `**`. Pulse conjoins repeated `requires` itself, and a spliced
        // clause may be a top-level `exists*`, which does not parse to the
        // right of a `**`. Separate clauses also read better when one of them
        // is a page of hand-written ownership.
        for clause in &req {
            out += &format!("  requires {}\n", clause);
        }
    }
    out += &format!("  returns  {} : {}\n", ret_name, ret);

    let mut bodies: Vec<String> = fresh.iter().map(|(_, _, s)| s.clone()).collect();
    bodies.extend(owned_post.iter().cloned());
    bodies.extend(post_props.iter().map(|p| format!("pure ({})", p)));
    // A postcondition that names a `__fp` wrapper is one that hands something
    // about that function on -- a validity, most of the time, and one the
    // body seeded itself. Reading it back off the assembled text is cruder
    // than tracking it, but it is exactly the question the body has to ask.
    let mut post_valid: HashSet<String> = HashSet::new();
    for clause in bodies.iter() {
        let mut rest = clause.as_str();
        while let Some(i) = rest.find("__fp") {
            if let Some(j) = rest[..i].rfind("func_") {
                post_valid.insert(rest[j + 5..i].to_string());
            }
            rest = &rest[i + 4..];
        }
    }
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
    if let Some(d) = &decreases {
        out += &format!("  decreases ({})\n", d);
    }

    // The `__fp` wrapper: the same contract, in the shape `of_fn_div` can
    // reflect. `valid` relates an address to a *flat* spec `x:a -> y:erased c
    // -> stt_div b (pre x y) (post x y)`, so the arguments become one tuple
    // and every binder becomes explicit; `pre_of`/`post_of` then read the
    // pre/post back off the wrapper's type, which is why the contract has to
    // be written out here rather than referred to.
    //
    // The witness type `c` is what makes a pointer parameter work. A function
    // taking a `T *` owns a `T` at it, and the value it owns is an implicit
    // binder -- which the flat shape forbids. So every implicit the
    // specification has, the permission of a `const` parameter as much as the
    // value behind a pointer or a `_ghost_arg`, becomes a component of `c`,
    // and the wrapper opens the tuple back up with a `let` inside the
    // contract. The caller of `call_div` then has to name the witness, which
    // is exactly the information an indirect call needs and cannot infer:
    // which object the callee is about to be handed.
    let simple = decay
        && decl.args.iter().all(|a| {
            matches!(
                a.mode,
                ParamMode::Regular | ParamMode::Const | ParamMode::Consumed
            )
        })
        && globals.is_empty()
        && contract_ok;
    let fp = if simple {
        let tys: Vec<String> = decl
            .args
            .iter()
            .map(|a| fstar_type(tds, &a.ty).unwrap())
            .collect();
        let names: Vec<String> = decl
            .args
            .iter()
            .enumerate()
            .map(|(i, a)| match &a.name {
                Some(n) => format!("var_{}", n.val),
                None => format!("arg_{}", i),
            })
            .collect();
        // The flat n-ary tuple is not nested pairs: arity 2 projects with
        // `fst`/`snd`, arity 3 and up with the `tupleN` field projectors.
        let tuple = |tys: &[String]| -> String {
            match tys.len() {
                0 => "unit".to_string(),
                1 => tys[0].clone(),
                _ => format!("({})", tys.join(" & ")),
            }
        };
        let projs = |n: usize, of: &str| -> Vec<String> {
            (0..n)
                .map(|i| match n {
                    1 => of.to_string(),
                    2 => format!("({} {})", if i == 0 { "fst" } else { "snd" }, of),
                    _ => format!("(Mktuple{}?._{} {})", n, i + 1, of),
                })
                .collect()
        };
        let n = tys.len();
        let domain = tuple(&tys);
        let aprojs = projs(n, "x_fp");
        // The witness, unlike the argument tuple, is folded to the RIGHT into
        // nested pairs rather than left flat. A caller of `call_div` does not
        // write the witness down -- it is inferred from the ownership being
        // handed over -- and the rule that makes that inference possible
        // (`eta_expanded_pair`) is binary. A flat `tuple3` is not two nested
        // `tuple2`s, so it would not fire, and a three-component witness would
        // be uninferrable for want of a rule rather than for want of
        // information.
        let wtys: Vec<String> = wits.iter().map(|(_, t, _)| t.clone()).collect();
        let witness = tuple(&wtys);
        let wprojs = projs(wits.len(), "(reveal w_fp)");
        let mut binds = String::new();
        for (nm, pj) in names.iter().zip(aprojs.iter()) {
            binds += &format!("let {} = {} in ", nm, pj);
        }
        // An erased implicit is re-hidden, so the binder has the type the
        // contract was written against and the text below is the same text.
        // An erased implicit is re-hidden, so the binder has the type the
        // contract was written against and the text below is the same text.
        for ((nm, _, erased), pj) in wits.iter().zip(wprojs.iter()) {
            binds += &format!(
                "let {} = {} in ",
                nm,
                if *erased {
                    format!("hide {}", pj)
                } else {
                    pj.clone()
                }
            );
        }
        let conj = |ps: &[String]| -> String {
            if ps.is_empty() {
                format!("({}emp)", binds)
            } else {
                format!("({}{})", binds, ps.join(" ** "))
            }
        };
        // `preserves` is sugar for a conjunct at both ends, and the flat shape
        // has no sugar, so it is written out on both sides here.
        let mut pre = preserved.clone();
        pre.extend(req.iter().cloned());
        let mut post: Vec<String> = preserved.clone();
        post.extend(bodies.iter().cloned());
        let post = if fresh.is_empty() {
            conj(&post)
        } else {
            let binders: Vec<String> = fresh
                .iter()
                .map(|(b, t, _)| format!("({}: {})", b, t))
                .collect();
            conj(&[format!(
                "(exists* {}. {})",
                binders.join(" "),
                if post.is_empty() {
                    "emp".to_string()
                } else {
                    post.join(" ** ")
                }
            )])
        };
        let call = if n == 0 {
            format!("func_{} ()", decl.name.val)
        } else {
            format!("func_{} {}", decl.name.val, aprojs.join(" "))
        };
        Some(format!(
            "divergent\n\
             fn {name}__fp (x_fp: {domain}) (w_fp: erased ({witness}))\n\
             \x20 requires prevent_lifting {pre}\n\
             \x20 returns  {ret_name} : {ret}\n\
             \x20 ensures  {post}\n\
             {{\n\
             \x20 let _ = w_fp;\n\
             \x20 {call}\n\
             }}\n\n",
            name = name,
            domain = domain,
            witness = witness,
            pre = conj(&pre),
            ret_name = ret_name,
            ret = ret,
            post = post,
            call = call,
        ))
    } else {
        None
    };

    let mut granted: HashSet<String> = owned
        .iter()
        .map(|o| o.base.clone())
        .chain(
            refines_value
                .iter()
                .filter(|(.., p)| contract_ok && slprop_refine(tds, p).is_some())
                .map(|(base, ..)| base.clone()),
        )
        .collect();
    // A contract with hand-written ownership in it is ownership Palow did not
    // put there and cannot read: what a spliced `_preserves` says about which
    // parameter it covers is the author's business. So one is taken as a grant
    // over everything, which is the same trust a spliced clause gets
    // everywhere else.
    if contract_ok && !(req_slprops.is_empty() && ens_slprops.is_empty()) {
        granted.extend(
            decl.args
                .iter()
                .filter_map(|a| a.name.as_ref().map(|n| n.val.to_string())),
        );
    }

    Ok(FnSurface {
        olens,
        ret_spliced: contract_ok && !(ret_slprops.is_empty() && ret_valued.is_empty()),
        req_props,
        post_valid,
        decl: out,
        owned,
        guarded,
        granted,
        spliced_own: contract_ok
            && (!(req_slprops.is_empty() && ens_slprops.is_empty()) || refine_own_spliced.take()),
        contract: contract_ok,
        fp,
        fp_wits: wits.len(),
        globals: globals.to_vec(),
        uses: spec.uses.take(),
        // A contract that was dropped granted nothing, so nothing may be
        // called through.
        valid_fps: if contract_ok {
            valid_fps.take()
        } else {
            HashSet::new()
        },
        freeables: if contract_ok {
            freeables.take()
        } else {
            HashMap::new()
        },
        consumed,
        ret_block,
        self_rec: decreases.is_some(),
    })
}

const HEADER: &str = r#"(* Generated by pal --palow.

   One C declaration in the Palow memory model: the F* type of every parameter,
   the ownership its contract needs, and -- where the translation covers it --
   the body. The module opens exactly the earlier declarations it names. See
   palow.md.

   Where the translation does not cover something, the contract is dropped and
   the body is `admit()`ed. Both make the specification weaker than the one PAL
   emits today rather than wrong; the count of them is the coverage
   measurement. *)
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
/// The machine shape of a bit-field's declared type: how many bytes it
/// spans, whether it is `_Bool`, and whether it is signed.
fn scalar_shape(tds: &Typedefs, ty: &Type) -> Option<(u64, bool, bool)> {
    match &tds.resolve(ty).val {
        TypeT::Bool => Some((1, true, false)),
        TypeT::Int { signed, width } => Some((*width as u64 / 8, false, *signed)),
        _ => None,
    }
}

/// Work out the storage unit a maximal run of bit-fields shares.
///
/// C does not say where a bit-field lives; the ABI does, and clang has
/// already decided, so the only thing to reconstruct is which bytes the run
/// occupies. That is the range from the first bit-field's bit offset to the
/// start of whatever comes next, narrowed to a width an unsigned integer
/// object can have. The unit is then an ordinary field of that type, and the
/// bit-fields are positions inside it.
///
/// `run` is `(name, declared type, bit offset, width)`; `limit` is the first
/// byte the unit may not touch.
fn bit_unit(
    tds: &Typedefs,
    run: &[(String, Rc<Type>, u64, u32)],
    limit: u64,
    loc: &Rc<SourceInfo>,
) -> Result<(String, Rc<Type>, u64, Vec<(String, BitPos)>), String> {
    let start_bit = run[0].2;
    if start_bit % 8 != 0 {
        return Err(format!(
            "bit-field `{}` starts a storage unit in the middle of a byte",
            run[0].0
        ));
    }
    let start = start_bit / 8;
    let end_bit = run.iter().map(|(_, _, o, w)| o + *w as u64).max().unwrap();
    let need = (end_bit - start_bit).div_ceil(8);
    // Every member has to have the same declared width, because the unit is
    // what a read of any of them yields and there is only one unit.
    let mut declared = None;
    for (n, ty, _, _) in run {
        let Some((bytes, boolean, signed)) = scalar_shape(tds, ty) else {
            return Err(format!(
                "bit-field `{}` is {}",
                n,
                describe(tds.resolve(ty))
            ));
        };
        if signed {
            return Err(format!("bit-field `{}` has a signed type", n));
        }
        if !boolean && declared.is_some_and(|d| d != bytes) {
            return Err(format!(
                "bit-field `{}` has a different width from the unit it shares",
                n
            ));
        }
        if !boolean {
            declared = Some(bytes);
        }
    }
    // Prefer the declared width, which is what the ABI allocated and what
    // makes the unit's type the one a member access already has.
    let us = [declared.unwrap_or(0), 1, 2, 4, 8]
        .into_iter()
        .find(|u| matches!(u, 1 | 2 | 4 | 8) && *u >= need && start % u == 0 && start + u <= limit)
        .ok_or_else(|| {
            format!(
                "the storage unit of bit-field `{}` is not an unsigned integer object",
                run[0].0
            )
        })?;
    if declared.is_some_and(|d| d != us) {
        return Err(format!(
            "bit-field `{}` is declared wider than the unit it shares",
            run[0].0
        ));
    }
    let mut members = Vec::new();
    for (n, ty, o, w) in run {
        let boolean = scalar_shape(tds, ty).unwrap().1;
        if boolean && *w != 1 {
            return Err(format!("`_Bool` bit-field `{}` is wider than one bit", n));
        }
        members.push((
            n.clone(),
            BitPos {
                unit_bits: (us * 8) as u32,
                off: (o - start_bit) as u32,
                width: *w,
                boolean,
            },
        ));
    }
    let ty = TypeT::Int {
        signed: false,
        width: (us * 8) as u32,
    }
    .with_loc(loc.clone());
    Ok((format!("bits{}", start), ty, start, members))
}

/// A field's `_refine` as a proposition about a single binder named `v`.
///
/// `seq` says what `v` stands for: an `_array` field's refinement is almost
/// always about its length, and a length is not part of the field's value --
/// the value is an address and the sequence lives in the struct's ownership
/// record -- so there `v` is the sequence and `this._length` reads it. For
/// every other field `v` is simply the value.
///
/// A clause naming a *sibling* field is deliberately not covered. It is
/// sayable in the record type, where an earlier field is in scope, but it
/// would also put an obligation on the write to the sibling, and that is a
/// separate piece of work. Returning `None` leaves the honest note in place.
fn field_invariant(tds: &Typedefs, env: &Env, fty: &Type, seq: bool) -> Option<String> {
    let (ps, _, _) = refinements(tds, fty).ok()?;
    let ps: Vec<_> = ps
        .into_iter()
        .filter(|p| slprop_refine(tds, p).is_none())
        .collect();
    let first = ps.first()?;
    let mut env = env.clone();
    env.push_var_decl(
        &Rc::<str>::from("this").with_loc(first.loc.clone()),
        Rc::new(peel(tds, fty).clone()),
        crate::env::LocalDeclKind::RValue,
    );
    let mut pointees = HashMap::new();
    let mut arrays = HashSet::new();
    let mut locals = HashMap::new();
    locals.insert("this".to_string(), "v".to_string());
    if seq {
        pointees.insert(
            "this".to_string(),
            (Some("v".to_string()), Some("v".to_string())),
        );
        arrays.insert("this".to_string());
    }
    let spec = Spec {
        tds,
        env: &env,
        pointees,
        olds: HashMap::new(),
        arrays,
        olens: HashMap::new(),
        owns: HashMap::new(),
        addrs: HashMap::new(),
        guarded: HashSet::new(),
        guards: RefCell::new(Vec::new()),
        ret: "v".to_string(),
        locals,
        uses: RefCell::new(HashSet::new()),
        signed_ok: false,
        valued: RefCell::new(Vec::new()),
    };
    let mut out = Vec::new();
    for p in &ps {
        // A clause the translation cannot state is no invariant at all: the
        // record type has to hold for *every* value, so half of one would be
        // worse than none.
        out.push(spec.prop(p, When::Pre).ok()?);
        if !spec.guards.borrow().is_empty() {
            return None;
        }
    }
    Some(out.join(" /\\ "))
}

fn collect_structs(tu: &TranslationUnit, tds: &mut Typedefs, env: &Env) -> Vec<Chunk> {
    let layouts = crate::layout::LayoutCtx::of_tu(tu);
    let mut code: Vec<Chunk> = Vec::new();
    for decl in &tu.decls {
        if let DeclT::UnionDefn(ud) = &decl.val {
            let mut c = collect_union(tds, &layouts, ud);
            c.origin = origin_of(decl);
            code.push(c);
            continue;
        }
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
        tds.aggregate_layouts
            .insert(format!("struct {}", name), (size, align));
        // Every field has to have a Palow type. Structs are processed in
        // declaration order, so a field of an earlier struct type works and a
        // field of a later one does not -- which is also all C allows.
        let mut fields = Vec::new();
        let mut bitfields: Vec<(String, BitField)> = Vec::new();
        let mut ok = true;
        let mut bad = String::new();
        // Resolve the declared fields into the ones the struct's value
        // records. A plain field is itself; a maximal run of bit-fields
        // collapses into the single unsigned object they share, and each of
        // them becomes a position inside it.
        let mut plan: Vec<(String, Rc<Type>, u64)> = Vec::new();
        let mut i = 0usize;
        while i < sd.fields.len() {
            let f = &sd.fields[i];
            let fname = f.val.name().val.to_string();
            if f.val.bit_width().is_none() {
                match layouts.offset_of(&key, &fname) {
                    Some(off) => plan.push((fname, f.val.logical_type(&f.loc), off)),
                    None => {
                        ok = false;
                        bad = format!("field `{}` has no byte offset", fname);
                        break;
                    }
                }
                i += 1;
                continue;
            }
            let mut j = i;
            let mut run = Vec::new();
            while j < sd.fields.len()
                && let Some(w) = sd.fields[j].val.bit_width()
            {
                let n = sd.fields[j].val.name().val.to_string();
                let Some(bo) = layouts.bit_offset_of(&key, &n) else {
                    break;
                };
                run.push((n, sd.fields[j].val.logical_type(&sd.fields[j].loc), bo, w));
                j += 1;
            }
            if run.len() != j - i || run.is_empty() {
                ok = false;
                bad = format!("bit-field `{}` has no bit offset", fname);
                break;
            }
            // The unit may not reach into the next field, nor past the end.
            let limit = sd.fields[j..]
                .iter()
                .find_map(|g| layouts.offset_of(&key, &g.val.name().val.to_string()))
                .unwrap_or(size);
            match bit_unit(tds, &run, limit, &f.loc) {
                Ok((uname, uty, uoff, members)) => {
                    if sd.fields.iter().any(|g| *g.val.name().val == *uname) {
                        ok = false;
                        bad = format!("field `{}` collides with a bit-field storage unit", uname);
                        break;
                    }
                    for (n, pos) in members {
                        bitfields.push((
                            n,
                            BitField {
                                unit: uname.clone(),
                                pos,
                            },
                        ));
                    }
                    plan.push((uname, uty, uoff));
                }
                Err(why) => {
                    ok = false;
                    bad = why;
                    break;
                }
            }
            i = j;
        }
        for (fname, fty, off) in plan {
            let (Some(shape), true) = (field_shape(tds, &fty), field_type(tds, &fty).is_some())
            else {
                ok = false;
                bad = format!("field `{}` is {}", fname, describe(tds.resolve(&fty)));
                break;
            };
            let Some(fsize) = shape.size(tds, &fty) else {
                ok = false;
                bad = format!("field `{}` has no size", fname);
                break;
            };
            // An `_array` field's refinement is about the sequence in the
            // ownership record; every other field's is about its value.
            let seq = extent(tds, &fty) == Some(Extent::Array) || flex_elem(tds, &fty).is_some();
            let inv = field_invariant(tds, env, &fty, seq);
            fields.push(StructField {
                name: fname,
                ty: fty,
                offset: off,
                size: fsize,
                shape,
                inv,
            });
        }
        if !ok || fields.is_empty() {
            if bad.is_empty() {
                bad = "it has no fields".to_string();
            }
            code.push(Chunk {
                module: format!("Struct_{}", name),
                code: format!("(* skipped struct {}: {} *)\n\n", name, bad),
                origin: origin_of(decl),
            });
            continue;
        }
        // The byte-level view needs every field to have one and to sit at a
        // byte offset of its own, so that the object splits into fields and
        // padding with nothing left over. An array field is excluded for now
        // only because the storage operations it would need are not generated
        // yet, not because anything about it resists the representation.
        //
        // The size limit is about the proof, not the model. `_reveal` has to
        // recognise each field's slice of the finished object through the
        // appends stacked above it, which is one lemma call per field per
        // region -- fine for the handful of fields a struct used as an array
        // element or a union member has, and hopeless for the 200-field
        // configuration records that appear in real headers. Those keep the
        // field-wise view, which is linear and which is all they are ever
        // used through.
        let has_bytes = fields.len() <= MAX_BYTE_LEVEL_FIELDS
            && fields
                .iter()
                .all(|f| matches!(f.shape, FieldShape::One { .. }) && has_repr(tds, &f.ty));
        let has_read = fields.iter().all(|f| readable_field(tds, &f.ty));
        tds.structs.insert(
            name.clone(),
            StructInfo {
                fields,
                bitfields,
                size,
                align,
                has_read,
                has_bytes,
            },
        );
        code.push(Chunk {
            module: format!("Struct_{}", name),
            code: emit_struct(tds, &name),
            origin: origin_of(decl),
        });
    }
    code
}

/// Generate the Palow type for one union. Every member has to have a
/// byte-level `_repr`, which is a stronger condition than a struct field's:
/// the union's own representation is defined by cases over the members'
/// representations of the same bytes, so a member whose ownership is defined
/// field-wise rather than over bytes -- a generated struct -- has nothing to
/// contribute to it.
fn collect_union(
    tds: &mut Typedefs,
    layouts: &crate::layout::LayoutCtx,
    ud: &crate::ir::UnionDefn,
) -> Chunk {
    let name = ud.name.val.to_string();
    let key = TypeRefKind::Union(ud.name.clone());
    let skip = |why: String| Chunk {
        module: format!("Union_{}", name),
        code: format!("(* skipped union {}: {} *)\n\n", name, why),
        origin: None,
    };
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
        return skip("it has no layout".to_string());
    };
    tds.aggregate_layouts
        .insert(format!("union {}", name), (size, align));
    let mut members = Vec::new();
    for f in &ud.fields {
        let mname = f.val.name().val.to_string();
        let mty = f.val.logical_type(&f.loc);
        // A member's own ownership has to be defined over *bytes*: the
        // members overlap, so the union's representation is a case split on
        // the same bytes and a member whose ownership is field-wise has
        // nothing to contribute to it. An array of such a member is fine --
        // `field_shape` has already asked the question of its element.
        let shape = match field_shape(tds, &mty) {
            Some(FieldShape::One { .. }) if !has_repr(tds, &mty) => None,
            other => other,
        };
        let (Some(shape), Some(_)) = (shape, field_type(tds, &mty)) else {
            return skip(format!(
                "member `{}` is {}, which has no byte-level `_repr`",
                mname,
                describe(tds.resolve(&mty))
            ));
        };
        let Some(msize) = shape.size(tds, &mty) else {
            return skip(format!("member `{}` has no size", mname));
        };
        if msize > size {
            return skip(format!("member `{}` is larger than the union", mname));
        }
        members.push(UnionMember {
            name: mname,
            ty: mty,
            shape,
            size: msize,
        });
    }
    if members.is_empty() {
        return skip("it has no members".to_string());
    }
    tds.unions.insert(
        name.clone(),
        UnionInfo {
            members,
            size,
            align,
        },
    );
    Chunk {
        module: format!("Union_{}", name),
        code: emit_union(tds, &name),
        origin: None,
    }
}

/// The generated code for one union: the tagged value type, its layout
/// constants, the byte-level representation, and per member the focus/unfocus
/// pair plus the `switch` that makes it the active one.
///
/// The value type is tagged even though the storage is not, which is how the
/// model says which member is live without putting a tag in memory. The
/// representation is deliberately *not* injective: bytes that represent one
/// member also represent any other member they happen to encode, and that
/// non-injectivity is exactly what makes type punning expressible rather than
/// a thing to be ruled out.
fn emit_union(tds: &Typedefs, name: &str) -> String {
    let ui = &tds.unions[name];
    let un = format!("union_{}", name);
    let mut c = String::new();

    // F* constructors have to be capitalised, so the tag is `Union_foo_x`
    // where the type is `union_foo`. C identifiers are unique within a
    // translation unit, so the pair of names cannot collide.
    let ctor = |m: &UnionMember| format!("Union_{}_{}", name, m.name);

    c += &format!("noeq type {} =\n", un);
    for m in &ui.members {
        c += &format!(
            "  | {} : v: ({}) -> {}\n",
            ctor(m),
            field_type(tds, &m.ty).unwrap(),
            un
        );
    }
    c += "\n";
    // An array arm is filled element by element, exactly as an array field
    // of a structure is, so the same recursion has to be in scope here.
    let mut fills: Vec<String> = Vec::new();
    for m in &ui.members {
        if let FieldShape::Array { pn, esize, len } = &m.shape {
            let name = fill_name(pn, *esize, *len);
            if !fills.contains(&name) {
                fills.push(name);
                let elem = fstar_type(tds, flat_array(tds, &m.ty).unwrap().0).unwrap();
                c += &emit_fill(pn, &elem, *esize, *len);
            }
        }
    }
    c += &format!("let {}_sizeof : SizeT.t = {}sz\n", un, ui.size);
    c += &format!("let {}_alignof : SizeT.t = {}sz\n\n", un, ui.align);

    c += &format!(
        "let {un}_repr (u: {un}) (b: bytes) : prop =\n  \
         len b == SizeT.v {un}_sizeof /\\\n  \
         (len b == SizeT.v {un}_sizeof ==>\n    (match u with\n",
        un = un
    );
    for m in &ui.members {
        c += &format!(
            "     | {} v -> {}\n",
            ctor(m),
            m.shape.repr_of("v", &format!("(slice b 0 {})", m.size))
        );
    }
    c += "    ))\n\n";

    // A generated struct joins its fields' byte ranges in offset order and
    // needs each length as a side condition, so every field type has to offer
    // the length under one name. For a union it is the first conjunct of the
    // representation; this gives it that name.
    c += &format!(
        "let {un}_repr_len (u: {un}) (b: bytes)\n  \
         : Lemma (requires {un}_repr u b) (ensures len b == SizeT.v {un}_sizeof)\n  \
         = ()\n\n",
        un = un
    );

    c += &format!(
        "let {un}_pts_to ([@@@mkey] a: ptr) (p: perm) (u: {un}) : slprop =\n  \
         exists* b. mem_pts_to a p b ** pure ({un}_repr u b)\n\n\
         let {un}_pts_to_uninit ([@@@mkey] a: ptr) : slprop =\n  \
         exists* b. mem_pts_to a 1.0R b ** pure (len b == SizeT.v {un}_sizeof)\n\n",
        un = un
    );

    for m in &ui.members {
        let mty = field_type(tds, &m.ty).unwrap();
        let k = ctor(m);
        let f = &m.name;
        let at = "a";
        let mem_pts_to = |p: &str, v: &str| m.shape.pts_to_at(at, p, v);
        let mem_uninit = m.shape.uninit_at(at);
        // The bytes past the member. A member as wide as the union still gets
        // one, of length zero: `mem_split` hands back a suffix either way and
        // a resource cannot simply be dropped, so treating the two cases alike
        // is shorter than telling them apart.
        c += &format!(
            "let {un}_rest_{f} (a: ptr) (p: perm) : slprop =\n  \
             exists* r. mem_pts_to (a +! {msz}sz) p r ** pure (len r == {rest})\n\n",
            un = un,
            f = f,
            msz = m.size,
            rest = ui.size - m.size
        );
        c += &format!(
            "ghost fn {un}_focus_{f} (a: ptr) (#p: perm) (#v: {mty})\n\
             \x20 requires {un}_pts_to a p ({k} v)\n\
             \x20 ensures  {pts}\n\
             \x20 ensures  {un}_rest_{f} a p\n\
             {{\n  \
             unfold {un}_pts_to a p ({k} v);\n  \
             with b. assert (mem_pts_to a p b ** pure ({un}_repr ({k} v) b));\n  \
             mem_split a {msz}sz;\n  \
             {conceal}\n  \
             fold {un}_rest_{f} a p;\n}}\n\n",
            un = un,
            f = f,
            k = k,
            pts = mem_pts_to("p", "v"),
            conceal = m
                .shape
                .conceal("a", "p", &format!("(slice b 0 {})", m.size), "v"),
            mty = mty,
            msz = m.size
        );
        c += &format!(
            "ghost fn {un}_unfocus_{f} (a: ptr) (#p: perm) (#v: {mty})\n\
             \x20 requires {pts}\n\
             \x20 requires {un}_rest_{f} a p\n\
             \x20 ensures  {un}_pts_to a p ({k} v)\n\
             {{\n  \
             {reveal}\n  \
             with bx. assert (mem_pts_to a p bx ** pure ({repr}));\n  \
             unfold {un}_rest_{f} a p;\n  \
             with r. assert (mem_pts_to (a +! {msz}sz) p r);\n  \
             mem_join a #p #bx #r {msz}sz;\n  \
             append_slice_left bx r;\n  \
             fold {un}_pts_to a p ({k} v);\n}}\n\n",
            un = un,
            f = f,
            k = k,
            pts = mem_pts_to("p", "v"),
            reveal = m.shape.reveal("a", "p", "v"),
            repr = m.shape.repr_of("v", "bx"),
            mty = mty,
            msz = m.size
        );
        // Making a member active is not a focus: the union may currently hold
        // any member at all, so there is no value to hand out, only storage.
        // It needs full permission for the same reason a write does.
        c += &format!(
            "ghost fn {un}_switch_{f} (a: ptr) (#u: {un})\n\
             \x20 requires {un}_pts_to a 1.0R u\n\
             \x20 ensures  {uninit}\n\
             \x20 ensures  {un}_rest_{f} a 1.0R\n\
             {{\n  \
             unfold {un}_pts_to a 1.0R u;\n  \
             with b. assert (mem_pts_to a 1.0R b ** pure ({un}_repr u b));\n  \
             mem_split a {msz}sz;\n  \
             {claim}\n  \
             fold {un}_rest_{f} a 1.0R;\n}}\n\n",
            un = un,
            f = f,
            uninit = mem_uninit,
            claim = m
                .shape
                .claim_uninit("a", &format!("(slice b 0 {})", m.size)),
            msz = m.size
        );
        // The same step from storage that has never held anything. A local
        // union starts out as bytes with nothing said about them, and `union
        // u; u.m = x;` is ordinary C, so making a member active has to be
        // reachable from there as well as from a union that already holds
        // something. The proof is the same one: only the length of the
        // storage is used.
        c += &format!(
            "ghost fn {un}_switch_uninit_{f} (a: ptr)\n\
             \x20 requires {un}_pts_to_uninit a\n\
             \x20 ensures  {uninit}\n\
             \x20 ensures  {un}_rest_{f} a 1.0R\n\
             {{\n  \
             unfold {un}_pts_to_uninit a;\n  \
             with b. assert (mem_pts_to a 1.0R b ** pure (len b == SizeT.v {un}_sizeof));\n  \
             mem_split a {msz}sz;\n  \
             {claim}\n  \
             fold {un}_rest_{f} a 1.0R;\n}}\n\n",
            un = un,
            f = f,
            uninit = mem_uninit,
            claim = m
                .shape
                .claim_uninit("a", &format!("(slice b 0 {})", m.size)),
            msz = m.size
        );
    }

    // The same three names the scalar layer publishes, so that a union can be
    // a struct field or an array element without anything downstream having to
    // know it is a union: storage in, storage out, and the loss of knowledge
    // in between.
    c += &format!(
        "ghost fn {un}_claim_uninit (a: ptr) (#b: bytes)\n\
         \x20 requires mem_pts_to a 1.0R b\n\
         \x20 requires pure (len b == SizeT.v {un}_sizeof)\n\
         \x20 ensures  {un}_pts_to_uninit a\n\
         {{\n  fold {un}_pts_to_uninit a;\n}}\n\n\
         ghost fn {un}_reveal_uninit (a: ptr)\n\
         \x20 requires {un}_pts_to_uninit a\n\
         \x20 ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SizeT.v {un}_sizeof)\n\
         {{\n  unfold {un}_pts_to_uninit a;\n}}\n\n\
         ghost fn {un}_conceal (a: ptr) (#p: perm) (#b: bytes) (#u: {un})\n\
         \x20 requires mem_pts_to a p b\n\
         \x20 requires pure ({un}_repr u b)\n\
         \x20 ensures  {un}_pts_to a p u\n\
         {{\n  fold {un}_pts_to a p u;\n}}\n\n\
         ghost fn {un}_reveal (a: ptr) (#p: perm) (#u: {un})\n\
         \x20 requires {un}_pts_to a p u\n\
         \x20 ensures  exists* b. mem_pts_to a p b ** pure ({un}_repr u b)\n\
         {{\n  unfold {un}_pts_to a p u;\n}}\n\n",
        un = un
    );
    c += &format!(
        "ghost fn {un}_forget (a: ptr) (#u: {un})\n\
         \x20 requires {un}_pts_to a 1.0R u\n\
         \x20 ensures  {un}_pts_to_uninit a\n\
         {{\n  unfold {un}_pts_to a 1.0R u;\n  fold {un}_pts_to_uninit a;\n}}\n\n\
         fn {un}_stack_alloc ()\n\
         \x20 requires emp\n\
         \x20 returns  a: ptr\n\
         \x20 ensures  {un}_pts_to_uninit a\n\
         {{\n  let a = mem_stack_alloc {un}_sizeof;\n  fold {un}_pts_to_uninit a;\n  a\n}}\n\n\
         fn {un}_stack_free (a: ptr)\n\
         \x20 requires {un}_pts_to_uninit a\n\
         \x20 ensures  emp\n\
         {{\n  unfold {un}_pts_to_uninit a;\n  mem_stack_free a;\n}}\n\n",
        un = un
    );
    // Storing a whole union value is the one operation that has to know which
    // member is live, and the value is where that is written down. The match
    // is on the *value*, not on memory, so nothing here reads a tag that C
    // does not store.
    c += &format!(
        "fn {un}_write_uninit (a: ptr) (x: {un})\n\
         \x20 requires {un}_pts_to_uninit a\n\
         \x20 ensures  {un}_pts_to a 1.0R x\n\
         {{\n  unfold {un}_pts_to_uninit a;\n  match x {{\n",
        un = un
    );
    for m in &ui.members {
        c += &format!(
            "    {k} v -> {{\n      \
             with b. assert (mem_pts_to a 1.0R b);\n      \
             mem_split a {msz}sz;\n      \
             {claim}\n      \
             {write}\n      \
             fold {un}_rest_{f} a 1.0R;\n      \
             {un}_unfocus_{f} a;\n      \
             rewrite ({un}_pts_to a 1.0R ({k} v)) as ({un}_pts_to a 1.0R x);\n    }}\n",
            k = ctor(m),
            f = m.name,
            claim = m
                .shape
                .claim_uninit("a", &format!("(slice b 0 {})", m.size)),
            write = m.shape.write_uninit("a", "v"),
            un = un,
            msz = m.size
        );
    }
    c += "  }\n}\n\n";
    c += &format!(
        "fn {un}_write (a: ptr) (x: {un}) (#u: erased {un})\n\
         \x20 requires {un}_pts_to a 1.0R u\n\
         \x20 ensures  {un}_pts_to a 1.0R x\n\
         {{\n  {un}_forget a;\n  {un}_write_uninit a x;\n}}\n\n",
        un = un
    );
    c
}

/// The generated code for one struct: the record, its layout constants, its
/// points-to, and per field a hole predicate with the focus/unfocus pair that
/// opens and closes it. The per-field triple is the same shape as the array
/// combinator's, on purpose: a field access and a subscript are the same
/// operation on a sub-range, and the emitter should not have to tell them
/// apart.
/// One sub-object that a struct's `_own` predicate covers: the pointee of an
/// owned pointer field, or of an owned pointer reached through one.
///
/// C's `struct simple { int x, *y, **z; }` describes three fields but four
/// objects: the struct, `*y`, `*z` and `**z`. Palow's `_pts_to` is the first
/// of those and nothing else -- it is the struct's own bytes, and `y` and `z`
/// are addresses held in them, not objects. The other three are what `_own`
/// names.
#[derive(Clone)]
struct OwnItem {
    /// Suffix of the spec record's field, `y` or `z_1`.
    name: String,
    /// The F\* type of the value held there.
    ty: String,
    /// The Palow name of its type, whose `_pts_to` states the ownership.
    pn: String,
    /// Its address, as an expression over the struct value `x` and the spec
    /// record `s`.
    at: String,
    /// The element size, when the field is an `_array` pointer and what it
    /// owns is therefore an extent rather than one object.
    ///
    /// The extent is left unconstrained here. A struct that knows its own
    /// length says so in a `_refine`, and that refinement is a clause about
    /// `Seq.length` of this very sequence -- so pinning the length in the
    /// predicate would be saying the same thing twice, in a place where a
    /// struct without such a refinement could not follow.
    esize: Option<u64>,
    /// The `_refine` written on the field, as a proposition about a binder
    /// named `v`. An `_array` field's refinement is about the extent behind
    /// the pointer, which is this sequence and nothing else, so this is where
    /// it can be made true of every value rather than only of parameters.
    inv: Option<String>,
}

impl OwnItem {
    /// The same item at a different address, which the gather needs: its
    /// ghost binders stand where the spec record's fields do.
    fn at(&self, at: String) -> OwnItem {
        OwnItem { at, ..self.clone() }
    }

    /// The ownership this item states, at a permission and a value.
    fn pts_to(&self, p: &str, v: &str) -> String {
        match self.esize {
            None => format!("{}_pts_to {} {} {}", self.pn, self.at, p, v),
            Some(es) => format!(
                "array_pts_to {}_repr {} {} {} {}",
                self.pn, es, self.at, p, v
            ),
        }
    }
}

/// The pointee of a pointer that carries ownership of what it points at, or
/// `None` when it does not.
///
/// Three kinds of pointer own nothing by design and are the reason this is a
/// question rather than a projection. `_plain` says the parameter is a bare
/// address; `_core_ref` says the pointer exists to break a cycle and carries
/// no predicate; and an array pointer points at an extent nothing here knows,
/// so there is no amount of memory to claim. `_nullable` is excluded for a
/// different reason: its ownership is real but sits behind a guard, and an
/// unconditional conjunct would be a claim about a null pointer.
fn owned_pointer<'a>(tds: &'a Typedefs, ty: &'a Type) -> Option<&'a Rc<Type>> {
    match &tds.resolve(ty).val {
        TypeT::Pointer(to, PointerKind::Unknown | PointerKind::Ref) => Some(to),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..) => owned_pointer(tds, t),
        _ => None,
    }
}

/// Walk one owned pointer as far as the chain of owned pointers goes.
///
/// `int **z` reaches two objects and the second one's address is the first
/// one's value, which is why the address of an item can mention the spec
/// record being defined. The walk stops at a struct or union: its own
/// `_pts_to` is claimed, but what *it* points at is left to whoever states it,
/// because following that would need the pointee's module -- which for a
/// mutually recursive pair does not exist yet -- and would make a
/// self-referential struct's predicate infinite.
fn own_chain(tds: &Typedefs, at: String, name: String, ty: &Type, out: &mut Vec<OwnItem>) {
    let (Some(pn), Some(fty)) = (palow_name(tds, ty), fstar_type(tds, ty)) else {
        return;
    };
    out.push(OwnItem {
        name: name.clone(),
        ty: fty,
        pn,
        at,
        esize: None,
        inv: None,
    });
    if let Some(to) = owned_pointer(tds, ty) {
        let to = to.clone();
        own_chain(
            tds,
            format!("((s).own_{})", name),
            format!("{}_1", name),
            &to,
            out,
        );
    }
}

/// Everything a struct's `_own` predicate covers, in field order.
fn own_items(tds: &Typedefs, si: &StructInfo, self_name: &str) -> Vec<OwnItem> {
    let mut out = Vec::new();
    if tds.plain_structs.contains(self_name) {
        return out;
    }
    for f in &si.fields {
        // An `_array` field owns an extent. Its length is not in the
        // predicate -- see `OwnItem::esize` -- so the sequence is simply as
        // long as it is, and a struct that knows better says so in a
        // `_refine` about this same sequence.
        if extent(tds, &f.ty) == Some(Extent::Array)
            && let Some(el) = pointee(tds, &f.ty)
            && has_repr(tds, el)
            && let (Some(pn), Some(ety), Some(es)) = (
                palow_name(tds, el),
                fstar_type(tds, el),
                palow_sizeof(tds, el),
            )
        {
            out.push(OwnItem {
                name: f.name.clone(),
                ty: format!("Seq.seq ({})", ety),
                pn,
                at: format!("((x).fld_{})", f.name),
                esize: Some(es),
                inv: f.inv.clone(),
            });
            continue;
        }
        let Some(to) = owned_pointer(tds, &f.ty) else {
            continue;
        };
        // A struct that points at itself, directly or through a chain, would
        // give an infinite conjunction. Stopping is the same choice C makes
        // when it asks for a forward declaration.
        if matches!(&tds.resolve(to).val, TypeT::TypeRef(TypeRefKind::Struct(n)) if &*n.val == self_name)
        {
            continue;
        }
        let to = to.clone();
        own_chain(
            tds,
            format!("((x).fld_{})", f.name),
            f.name.clone(),
            &to,
            &mut out,
        );
    }
    out
}

/// The second of a struct's two predicates: what the pointers *inside* it own.
///
/// Palow's `_pts_to` is deliberately shallow. It says which bytes the object
/// occupies and what values they encode, and a pointer field's value is an
/// address and nothing more -- which is what makes two views of the same
/// bytes agree, and what lets a struct be an array element or a union member.
/// But almost every C struct that holds a pointer means to own what it points
/// at, and a function taking one has to be able to say so without writing the
/// conjunction out by hand.
///
/// So ownership is a separate predicate over the struct's *value*, not its
/// address: `_own x p s` claims the objects reachable from the pointers in
/// `x`, and `s` records their values. Keeping it separate is what makes it
/// optional -- a `_pts_to` on its own is still a legitimate, and much
/// cheaper, thing to hold -- and it is also the only way the two can carry
/// different fractional permissions, which is what sharing a structure while
/// mutating through one of its pointers needs.
fn emit_struct_own(tds: &Typedefs, name: &str) -> String {
    let si = &tds.structs[name];
    let sn = format!("struct_{}", name);
    let items = own_items(tds, si, name);
    if items.is_empty() {
        return String::new();
    }
    let mut c = String::new();
    c += &format!(
        "noeq type {}_own_spec = {{ {} }}\n\n",
        sn,
        items
            .iter()
            .map(|i| format!("own_{}: {}", i.name, refined_ty(&i.ty, i.inv.as_ref())))
            .collect::<Vec<_>>()
            .join("; ")
    );
    let conj = |val: &dyn Fn(&OwnItem) -> String| -> String {
        items
            .iter()
            .map(|i| i.pts_to("p", &val(i)))
            .collect::<Vec<_>>()
            .join(" **\n  ")
    };
    let from_spec = |i: &OwnItem| format!("((s).own_{})", i.name);
    c += &format!(
        "let {sn}_own ([@@@mkey] x: {sn}) (p: perm) (s: {sn}_own_spec) : slprop =\n  {body}\n\n",
        sn = sn,
        body = conj(&from_spec)
    );
    c += &format!(
        "ghost fn {sn}_own_scatter (x: {sn}) (#p: perm) (#s: {sn}_own_spec)\n\
         \x20 requires {sn}_own x p s\n\
         {ens}\n\
         {{\n  unfold {sn}_own x p s;\n}}\n\n",
        sn = sn,
        ens = items
            .iter()
            .map(|i| format!("  ensures  {}", i.pts_to("p", &from_spec(i))))
            .collect::<Vec<_>>()
            .join("\n")
    );
    // The gather takes each value as its own ghost argument, because the
    // caller holds the pieces at values Pulse has to be free to unify. The
    // arguments are in chain order, so that the address of a later one can be
    // an earlier one's value -- which is exactly what `**z` is.
    let arg = |i: &OwnItem| format!("own_{}", i.name);
    let at_args = |i: &OwnItem| -> String {
        let mut a = i.at.clone();
        for j in &items {
            a = a.replace(&format!("((s).own_{})", j.name), &arg(j));
        }
        a
    };
    c += &format!(
        "ghost fn {sn}_own_gather (x: {sn}) (#p: perm) {binders}\n\
         {req}\n\
         \x20 ensures  {sn}_own x p ({{ {rec_} }})\n\
         {{\n  fold {sn}_own x p ({{ {rec_} }});\n}}\n\n",
        sn = sn,
        binders = items
            .iter()
            .map(|i| format!("(#{}: {})", arg(i), refined_ty(&i.ty, i.inv.as_ref())))
            .collect::<Vec<_>>()
            .join(" "),
        req = items
            .iter()
            .map(|i| format!("  requires {}", i.at(at_args(i)).pts_to("p", &arg(i))))
            .collect::<Vec<_>>()
            .join("\n"),
        rec_ = items
            .iter()
            .map(|i| format!("own_{} = {}", i.name, arg(i)))
            .collect::<Vec<_>>()
            .join("; ")
    );
    c
}

/// Whether a field's `_refine` is about the sequence in the struct's ownership
/// record rather than about the value the struct itself holds. An `_array`
/// field is the case: its value is an address, and the only thing anyone
/// writes a refinement about is how long the extent behind it is.
/// Whether a type carries a `_refine` that is a proposition about its value,
/// as opposed to one that is ownership. Only the first kind is something a
/// generated record type could have carried.
fn has_pure_refine(tds: &Typedefs, ty: &Type) -> bool {
    match refinements(tds, ty) {
        Ok((ps, us, _)) => !us.is_empty() || ps.iter().any(|p| slprop_refine(tds, p).is_none()),
        Err(_) => true,
    }
}

fn own_kind(tds: &Typedefs, ty: &Type) -> bool {
    extent(tds, ty) == Some(Extent::Array) && flex_elem(tds, ty).is_none()
}

/// An F\* type with a field's invariant attached, when there is one. The
/// refinement's own binder is always `v`, which is what lets the same rendered
/// text serve at every site that has to produce such a value.
fn refined_ty(ty: &str, inv: Option<&String>) -> String {
    match inv {
        Some(p) => format!("(v: {} {{ {} }})", ty, p),
        None => ty.to_string(),
    }
}

fn emit_struct(tds: &Typedefs, name: &str) -> String {
    let si = &tds.structs[name];
    let sn = format!("struct_{}", name);
    let mut c = String::new();

    // A `_refine` written on a *field* is an invariant of the struct type, so
    // it goes on the field's type in the record below and every value of the
    // type has it. What cannot go there says so here: a clause naming a
    // sibling field, which is sayable in the record but would also put an
    // obligation on every write to the sibling, and that is not yet done.
    //
    // An *ownership* clause on a field is a different matter and is not
    // dropped. It could never have gone on the record type -- an F\* type
    // cannot hold an slprop -- so the contract states it instead, at every
    // position a contract has: a parameter that is such a struct, a parameter
    // that points at one, and a result. That is the same place the old model
    // puts it, in the struct predicate rather than in the struct type.
    for f in &si.fields {
        if refined(tds, &f.ty) && f.inv.is_none() && has_pure_refine(tds, &f.ty) {
            c += &format!(
                "(* contract dropped: the `_refine` on field `{}` is not a \
                 property of the field's value alone *)\n",
                f.name
            );
        }
    }

    c += &format!(
        "noeq type {} = {{ {} }}\n\n",
        sn,
        si.fields
            .iter()
            .map(|f| {
                format!(
                    "fld_{}: {}",
                    f.name,
                    // An `_array` field's invariant is about the sequence, not
                    // about the address the value holds, so it belongs on the
                    // ownership record instead; see `emit_struct_own`.
                    refined_ty(
                        &field_type(tds, &f.ty).unwrap(),
                        f.inv.as_ref().filter(|_| !own_kind(tds, &f.ty))
                    )
                )
            })
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
            "ghost fn {sn}_unfocus_{f} (a: ptr) (#p: perm) (#x: {sn}) (#y: {rfty})\n\
             \x20 requires {sn}_hole_{f} a p x\n\
             \x20 requires {owned}\n\
             \x20 ensures  {sn}_pts_to a p {upd}\n\
             {{\n  unfold {sn}_hole_{f} a p x;\n  fold {sn}_pts_to a p {upd};\n}}\n\n",
            sn = sn,
            f = f.name,
            rfty = refined_ty(&fty, f.inv.as_ref().filter(|_| !own_kind(tds, &f.ty))),
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
    c += &emit_struct_own(tds, name);
    c += &emit_struct_storage(tds, name, &gaps);
    c += &emit_struct_bytes(tds, name, &gaps);
    c
}

/// One contiguous piece of a struct object: either a field or the padding
/// between two of them. Ordering the pieces by offset turns the object into a
/// partition, which is what both directions of the byte-level view walk.
enum Region<'a> {
    Field(&'a StructField),
    Gap(u64, u64),
}

impl Region<'_> {
    fn offset(&self) -> u64 {
        match self {
            Region::Field(f) => f.offset,
            Region::Gap(off, _) => *off,
        }
    }
    fn size(&self) -> u64 {
        match self {
            Region::Field(f) => f.size,
            Region::Gap(_, len) => *len,
        }
    }
}

/// The byte-level view of a struct: a `_repr` relating a value to the object's
/// bytes, and the two ghost functions that move between it and the field-wise
/// `_pts_to`.
///
/// Both views are kept, rather than one being defined from the other, because
/// they answer different questions. Field-wise ownership is what a field
/// access needs and what lets two fields carry different fractional
/// permissions; the byte-level one is what an array element or a union member
/// has to be, and it is the only one that says anything about the padding.
///
/// The proof is a partition argument in two directions. `_reveal` reveals each
/// field's bytes and joins the pieces left to right; `_conceal` splits the
/// object right to left and conceals each piece back into its field. Both
/// orders are chosen so that every intermediate address stays `a +! <absolute
/// offset>`: joining right to left, or splitting left to right, would nest the
/// arithmetic into `((a +! 4) +! 4) +! 1` and the solver does not see through
/// that.
fn emit_struct_bytes(tds: &Typedefs, name: &str, gaps: &[(u64, u64)]) -> String {
    let si = &tds.structs[name];
    if !si.has_bytes {
        return String::new();
    }
    let sn = format!("struct_{}", name);

    let mut regions: Vec<Region> = si
        .fields
        .iter()
        .map(Region::Field)
        .chain(gaps.iter().map(|(off, n)| Region::Gap(*off, *n)))
        .collect();
    regions.sort_by_key(|r| r.offset());

    let at = |off: u64| {
        if off == 0 {
            "a".to_string()
        } else {
            format!("(a +! {}sz)", off)
        }
    };
    let pn_of = |f: &StructField| match &f.shape {
        FieldShape::One { pn } => pn.clone(),
        _ => unreachable!(),
    };

    // The representation pins the fields and says nothing about the padding,
    // which is exactly what C guarantees: the gaps hold unspecified values,
    // and two objects with equal fields may differ there.
    let mut c = format!(
        "let {sn}_repr (x: {sn}) (b: bytes) : prop =\n  \
         len b == SizeT.v {sn}_sizeof /\\\n  \
         (len b == SizeT.v {sn}_sizeof ==>\n",
        sn = sn
    );
    let conj: Vec<String> = si
        .fields
        .iter()
        .map(|f| {
            format!(
                "    {}_repr x.fld_{} (slice b {} {})",
                pn_of(f),
                f.name,
                f.offset,
                f.offset + f.size
            )
        })
        .collect();
    c += &format!("{})\n\n", conj.join(" /\\\n"));

    c += &format!(
        "let {sn}_repr_len (x: {sn}) (b: bytes)\n  \
         : Lemma (requires {sn}_repr x b) (ensures len b == SizeT.v {sn}_sizeof)\n  \
         = ()\n\n",
        sn = sn
    );

    // What `calloc` gives back is a value only if the type says an all-zero
    // object is one. Each field contributes its own reason, and the padding
    // contributes nothing -- the representation says nothing about it, which
    // is why an all-zero object is representable at all.
    // A field invariant can rule the all-zero object out -- `_refine(this > 0)`
    // does -- and then there is no such value to state the lemma about. That
    // is not a gap: it is the invariant doing its job, and the `calloc` that
    // wanted it has to fail instead.
    let zeroable = si
        .fields
        .iter()
        .all(|f| f.inv.is_none() || own_kind(tds, &f.ty));
    if zeroable
        && let Some(proofs) = si
            .fields
            .iter()
            .map(|f| zero_repr_proof(tds, &f.ty))
            .collect::<Option<Vec<_>>>()
    {
        let zero = si
            .fields
            .iter()
            .map(|f| Ok(format!("fld_{} = {}", f.name, zero_value(tds, &f.ty)?)))
            .collect::<Result<Vec<_>, String>>();
        if let Ok(zero) = zero {
            let mut steps: Vec<String> = proofs.into_iter().flatten().collect();
            steps.push("()".to_string());
            c += &format!(
                "let {sn}_repr_zero (_: unit)\n  \
                 : Lemma ({sn}_repr ({{ {z} }}) (zeroed (SizeT.v {sn}_sizeof)))\n  \
                 = {steps}\n\n",
                sn = sn,
                z = zero.join("; "),
                steps = steps.join(" ")
            );
        }
    }

    // ---- reveal: fields to bytes ----
    let mut r = format!(
        "  unfold {sn}_pts_to a p x;\n  unfold {sn}_padding a p;\n",
        sn = sn
    );
    let mut accs: Vec<String> = Vec::new();
    for (k, reg) in regions.iter().enumerate() {
        let v = format!("r{}", k);
        match reg {
            Region::Field(f) => {
                let pn = pn_of(f);
                let val = format!("x.fld_{}", f.name);
                r += &format!(
                    "  rewrite ({pn}_pts_to (a +! {sn}_offsetof_{f}) p {val})\n    \
                     as ({pn}_pts_to {at} p {val});\n",
                    pn = pn,
                    sn = sn,
                    f = f.name,
                    val = val,
                    at = at(f.offset)
                );
                r += &format!("  {}_reveal {};\n", pn, at(f.offset));
                r += &format!(
                    "  with {v}. assert (mem_pts_to {at} p {v} ** pure ({pn}_repr {val} {v}));\n",
                    v = v,
                    at = at(f.offset),
                    pn = pn,
                    val = val
                );
                r += &format!("  {}_repr_len {} {};\n", pn, val, v);
            }
            Region::Gap(off, n) => {
                r += &format!(
                    "  with {v}. assert (mem_pts_to {at} p {v} ** pure (len {v} == {n}));\n",
                    v = v,
                    at = at(*off),
                    n = n
                );
            }
        }
        accs.push(if k == 0 {
            v
        } else {
            format!("(append {} {})", accs[k - 1], v)
        });
    }
    for reg in regions.iter().skip(1) {
        r += &format!("  mem_join a {}sz;\n", reg.offset());
    }
    // Every field's slice of the finished object has to be recognised as the
    // bytes that field was revealed to. Peeling the appends off from the
    // outside is what does it, one step per region above the field.
    for (j, reg) in regions.iter().enumerate() {
        let Region::Field(f) = reg else { continue };
        let (lo, hi) = (f.offset, f.offset + f.size);
        for k in (j + 1..regions.len()).rev() {
            r += &format!(
                "  slice_append_left_at {} r{} {} {};\n",
                accs[k - 1],
                k,
                lo,
                hi
            );
        }
        if j > 0 {
            r += &format!("  append_slice_right {} r{};\n", accs[j - 1], j);
        }
    }
    r += &format!(
        "  assert (pure ({sn}_repr x {acc}));\n",
        sn = sn,
        acc = accs[regions.len() - 1]
    );
    c += &format!(
        "ghost fn {sn}_reveal (a: ptr) (#p: perm) (#x: {sn})\n\
         \x20 requires {sn}_pts_to a p x\n\
         \x20 ensures  exists* b. mem_pts_to a p b ** pure ({sn}_repr x b)\n\
         {{\n{r}}}\n\n",
        sn = sn,
        r = r
    );

    // ---- conceal: bytes to fields ----
    let mut w = String::new();
    let mut hi = si.size;
    for reg in regions.iter().skip(1).rev() {
        let off = reg.offset();
        w += &format!("  mem_split a {}sz;\n", off);
        w += &format!("  slice_prefix b {hi} 0 {off};\n", hi = hi, off = off);
        w += &format!("  slice_prefix b {hi} {off} {hi};\n", hi = hi, off = off);
        hi = off;
    }
    for f in &si.fields {
        let pn = pn_of(f);
        w += &format!(
            "  {pn}_conceal {at} #p #(slice b {lo} {hi}) #(x.fld_{f});\n",
            pn = pn,
            at = at(f.offset),
            lo = f.offset,
            hi = f.offset + f.size,
            f = f.name
        );
        w += &format!(
            "  rewrite ({pn}_pts_to {at} p x.fld_{f})\n    \
             as ({pn}_pts_to (a +! {sn}_offsetof_{f}) p x.fld_{f});\n",
            pn = pn,
            at = at(f.offset),
            sn = sn,
            f = f.name
        );
    }
    c += &format!(
        "ghost fn {sn}_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: {sn})\n\
         \x20 requires mem_pts_to a p b\n\
         \x20 requires pure ({sn}_repr x b)\n\
         \x20 ensures  {sn}_pts_to a p x\n\
         {{\n{w}  fold {sn}_padding a p;\n  fold {sn}_pts_to a p x;\n}}\n\n",
        sn = sn,
        w = w
    );

    // The adapters that make the struct an array element. `elem_pts_to` is
    // the generic array layer's view of one slot, stated over the element's
    // representation, so these are the byte-level view read in the other
    // direction and nothing more.
    c += &format!(
        "ghost fn {sn}_of_elem (a: ptr) (#p: perm) (#x: {sn})\n\
         \x20 requires elem_pts_to {sn}_repr a p x\n\
         \x20 ensures  {sn}_pts_to a p x\n\
         {{\n  elem_reveal {sn}_repr a;\n  {sn}_conceal a #p #_ #x;\n}}\n\n\
         ghost fn {sn}_to_elem (a: ptr) (#p: perm) (#x: {sn})\n\
         \x20 requires {sn}_pts_to a p x\n\
         \x20 ensures  elem_pts_to {sn}_repr a p x\n\
         {{\n  {sn}_reveal a;\n  elem_conceal {sn}_repr a #p #_ #x;\n}}\n\n",
        sn = sn
    );
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
/// The name of the pair of functions that fills an array field of `len`
/// elements of type `pn`. One per shape rather than one per field: two fields
/// of the same element type and length need the same code.
fn fill_name(pn: &str, esize: u64, len: u64) -> String {
    format!("array_{}_{}_{}", pn, esize, len)
}

/// Filling an array field from a value, which is the one part of a structure's
/// write-only view that is not a fold: going from storage to holding `vs`
/// genuinely writes bytes, and there are `len` of them to write.
///
/// It is a recursion on the index rather than a `while` loop because a `while`
/// in Pulse is divergent, and divergence here would spread to every function
/// that declares such a structure. The index is a real argument, and the
/// measure is how much of the array is left.
fn emit_fill(pn: &str, elem: &str, esize: u64, len: u64) -> String {
    let f = fill_name(pn, esize, len);
    let at = format!("(a +! ({}sz `SizeT.mul` k))", esize);
    let tmpl = "\
fn rec {f}_from (a: ptr) (vs: (s: Seq.seq {t} {{ Seq.length s == {n} }})) (k: SizeT.t)
                (#xs: erased (xs: Seq.seq (option {t}) {{ Seq.length xs == {n} }}))
  requires array_pts_to (maybe_repr {pn}_repr {es}) {es} a 1.0R xs
  requires pure (SizeT.v k <= {n} /\\
                 (forall (j: nat). j < SizeT.v k ==> Seq.index xs j == Some (Seq.index vs j)))
  ensures  array_pts_to {pn}_repr {es} a 1.0R vs
  decreases ({n} - SizeT.v k)
{{
  if (SizeT.lt k {n}sz) {{
    array_focus (maybe_repr {pn}_repr {es}) a {es}sz k ({es}sz `SizeT.mul` k);
    elem_maybe_reveal {pn}_repr {es}sz {at};
    {pn}_claim_uninit {at};
    {pn}_write_uninit {at} (Seq.index vs (SizeT.v k));
    {pn}_to_elem {at};
    elem_maybe_put {pn}_repr {es}sz {at};
    array_unfocus (maybe_repr {pn}_repr {es}) a {es}sz k ({es}sz `SizeT.mul` k);
    {f}_from a vs (k `SizeT.add` 1sz);
  }} else {{
    array_claim_all {pn}_repr a {es}sz vs;
  }}
}}

fn {f}_fill (a: ptr) (vs: (s: Seq.seq {t} {{ Seq.length s == {n} }}))
  requires array_pts_to_uninit {pn}_repr {es} {n} a
  ensures  array_pts_to {pn}_repr {es} a 1.0R vs
{{
  unfold array_pts_to_uninit {pn}_repr {es} {n} a;
  {f}_from a vs 0sz;
}}

fn rec {f}_upto (a: ptr) (k: SizeT.t) (acc: (s: Seq.seq {t} {{ Seq.length s == SizeT.v k }}))
                (#p: perm) (#xs: erased (xs: Seq.seq {t} {{ Seq.length xs == {n} }}))
  preserves array_pts_to {pn}_repr {es} a p xs
  requires pure (SizeT.v k <= {n} /\\
                 (forall (j: nat). j < SizeT.v k ==> Seq.index acc j == Seq.index xs j))
  returns  r : (s: Seq.seq {t} {{ Seq.length s == {n} }})
  ensures  pure (r == reveal xs)
  decreases ({n} - SizeT.v k)
{{
  if (SizeT.lt k {n}sz) {{
    array_focus {pn}_repr a {es}sz k ({es}sz `SizeT.mul` k);
    {pn}_of_elem {at};
    let v = {pn}_read {at};
    {pn}_to_elem {at};
    array_unfocus_read {pn}_repr a {es}sz k ({es}sz `SizeT.mul` k);
    {f}_upto a (k `SizeT.add` 1sz) (Seq.snoc acc v)
  }} else {{
    Seq.lemma_eq_intro acc (reveal xs);
    acc
  }}
}}

fn {f}_read (a: ptr) (#p: perm) (#xs: erased (xs: Seq.seq {t} {{ Seq.length xs == {n} }}))
  preserves array_pts_to {pn}_repr {es} a p xs
  returns  r : (s: Seq.seq {t} {{ Seq.length s == {n} }})
  ensures  pure (r == reveal xs)
{{
  {f}_upto a 0sz Seq.empty
}}

";
    tmpl.replace("{f}", &f)
        .replace("{pn}", pn)
        .replace("{t}", elem)
        .replace("{es}", &esize.to_string())
        .replace("{n}", &len.to_string())
        .replace("{at}", &at)
        .replace("{{", "{")
        .replace("}}", "}")
}

fn emit_struct_storage(tds: &Typedefs, name: &str, gaps: &[(u64, u64)]) -> String {
    let si = &tds.structs[name];
    let sn = format!("struct_{}", name);
    // A field with no write-only view keeps the whole struct out of automatic
    // storage: there would be no way to hand back what was never claimed.
    let mut uninit = Vec::new();
    for f in &si.fields {
        // A nested struct field would need its own `_claim_uninit`, which the
        // generated layer does not have yet: the carve stops at the scalars.
        // An array field's element type was already checked for a
        // representation when the shape was worked out; it is the field's own
        // type, which is not a scalar, that `has_repr` rejects.
        let ok = match &f.shape {
            FieldShape::One { .. } => has_repr(tds, &f.ty),
            FieldShape::Array { .. } => true,
            FieldShape::Flex { .. } => false,
        };
        let u = if ok {
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
    let mut fills: Vec<String> = Vec::new();
    for f in &si.fields {
        if let FieldShape::Array { pn, esize, len } = &f.shape {
            let name = fill_name(pn, *esize, *len);
            if !fills.contains(&name) {
                fills.push(name);
                let elem = fstar_type(tds, flat_array(tds, &f.ty).unwrap().0).unwrap();
                c += &emit_fill(pn, &elem, *esize, *len);
            }
        }
    }
    c += &format!(
        "let {}_pts_to_uninit (a: ptr) : slprop =\n  {} **\n  {}_padding a 1.0R\n\n",
        sn,
        uninit.join(" **\n  "),
        sn
    );

    // `struct S s; s.f = ...; s.g = ...;` is ordinary C: the object is built
    // one field at a time, and between the two statements it is neither
    // storage nor a value but a mixture. The two halves of that are these.
    // `scatter_uninit` gives up the object and keeps its fields' storage --
    // which is all `_pts_to_uninit` ever was, so the proof is an `unfold` --
    // and `gather` puts a value back together out of fields that now hold
    // one. Nothing in between is a struct, which is exactly why neither the
    // focus nor the whole-object write could express it.
    // A pointer to an object is a pointer to its first field, and a scalar
    // points-to already says that its address is not null and has a
    // provenance. That is worth stating at the object, because a predicate
    // over a linked structure is where the null case has to be ruled out and
    // the caller has no reason to know which field sits at offset zero.
    if let Some(first) = si.fields.iter().find(|f| f.offset == 0) {
        if let FieldShape::One { pn } = &first.shape {
            if !matches!(
                tds.resolve(&first.ty).val,
                TypeT::TypeRef(..) | TypeT::FixedArray(..)
            ) {
                c += &format!(
                    "ghost fn {sn}_pts_to_not_null (a: ptr) (#p: perm) (#x: {sn})\n\
                     \x20 preserves {sn}_pts_to a p x\n\
                     \x20 ensures   pure (not (is_null a) /\\ Some? (prov_of a))\n\
                     {{\n\x20 {sn}_focus_{f} a;\n\
                     \x20 {pn}_pts_to_not_null (a +! {sn}_offsetof_{f});\n\
                     \x20 {sn}_unfocus_read_{f} a;\n}}\n\n",
                    sn = sn,
                    pn = pn,
                    f = first.name
                );
            }
        }
    }

    c += &format!(
        "ghost fn {sn}_scatter_uninit (a: ptr)\n\
         \x20 requires {sn}_pts_to_uninit a\n\
         \x20 ensures  {u}\n\
         \x20 ensures  {sn}_padding a 1.0R\n\
         {{\n  unfold {sn}_pts_to_uninit a;\n}}\n\n",
        sn = sn,
        u = uninit.join("\n\x20 ensures  ")
    );
    // The way back for an object that was scattered and then abandoned:
    // a local that went out of scope before every field had been written.
    c += &format!(
        "ghost fn {sn}_gather_uninit (a: ptr)\n\
         \x20 requires {u}\n\
         \x20 requires {sn}_padding a 1.0R\n\
         \x20 ensures  {sn}_pts_to_uninit a\n\
         {{\n  fold {sn}_pts_to_uninit a;\n}}\n\n",
        sn = sn,
        u = uninit.join("\n\x20 requires ")
    );
    {
        let binders: Vec<String> = si
            .fields
            .iter()
            .map(|f| {
                let elem = match flat_array(tds, &f.ty) {
                    Some((t, _)) => fstar_type(tds, t),
                    None => fstar_type(tds, &f.ty),
                }
                .unwrap_or_else(|| "unit".to_string());
                format!(
                    "(#val_{}: {})",
                    f.name,
                    refined_ty(
                        &f.shape.value_type(&elem),
                        f.inv.as_ref().filter(|_| !own_kind(tds, &f.ty))
                    )
                )
            })
            .collect();
        let value = if si.fields.is_empty() {
            "()".to_string()
        } else {
            format!(
                "({{ {} }})",
                si.fields
                    .iter()
                    .map(|f| format!("fld_{} = val_{}", f.name, f.name))
                    .collect::<Vec<_>>()
                    .join("; ")
            )
        };
        let reqs: Vec<String> = si
            .fields
            .iter()
            .map(|f| {
                f.shape.pts_to(
                    &format!("(a +! {}_offsetof_{})", sn, f.name),
                    &format!("val_{}", f.name),
                )
            })
            .collect();
        c += &format!(
            "ghost fn {sn}_gather (a: ptr) (#p: perm) {b}\n\
             \x20 requires {r}\n\
             \x20 requires {sn}_padding a p\n\
             \x20 ensures  {sn}_pts_to a p {v}\n\
             {{\n  fold {sn}_pts_to a p {v};\n}}\n\n",
            sn = sn,
            b = binders.join(" "),
            r = if reqs.is_empty() {
                "emp".to_string()
            } else {
                reqs.join("\n\x20 requires ")
            },
            v = value
        );
    }

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

    // Each split has to be followed immediately by the claim of the piece it
    // just cut off, rather than running all the splits and then all the
    // claims. Both orders are correct; they cost very differently. `mem_split`
    // describes its halves as `slice` of what it was given, so splitting the
    // same chunk `n` times leaves the last piece under `n` nested slices, and
    // doing all the splits first means the context holds all `n` of those at
    // once -- quadratic in the number of fields, and it is the single most
    // expensive thing the emitter produces for a wide struct. Claiming a piece
    // consumes its byte term, so interleaving keeps exactly one live at a
    // time. On a forty-field struct this alone is 40.7s to 10.1s.
    let claim_at = |f: &StructField, alloc: &mut String| match &f.shape {
        FieldShape::One { pn } => {
            *alloc += &format!("  {}_claim_uninit {};\n", pn, at(f.offset));
            *alloc += &format!(
                "  rewrite ({pn}_pts_to_uninit {off})\n    as ({pn}_pts_to_uninit (a +! {sn}_offsetof_{f}));\n",
                pn = pn,
                off = at(f.offset),
                sn = sn,
                f = f.name
            );
        }
        FieldShape::Flex { .. } => *alloc += NO_FLEX_STORAGE,
        FieldShape::Array { pn, esize, len } => {
            *alloc += &format!(
                "  array_claim_all_uninit {}_repr {} {}sz {}sz;\n",
                pn,
                at(f.offset),
                esize,
                len
            );
            *alloc += &format!(
                "  rewrite (array_pts_to_uninit {pn}_repr {es} {n} {off})\n    as (array_pts_to_uninit {pn}_repr {es} {n} (a +! {sn}_offsetof_{f}));\n",
                pn = pn,
                es = esize,
                n = len,
                off = at(f.offset),
                sn = sn,
                f = f.name
            );
        }
    };
    let field_at = |off: u64| si.fields.iter().find(|f| f.offset == off);
    let mut alloc = String::new();
    for off in bounds.iter().rev() {
        alloc += &format!("  mem_split a {}sz;\n", off);
        if let Some(f) = field_at(*off) {
            claim_at(f, &mut alloc);
        }
    }
    if let Some(f) = field_at(0) {
        claim_at(f, &mut alloc);
    }
    // Claiming raw storage at this type is the carve on its own; a stack
    // allocation is that plus the allocation. Separating them is what lets a
    // struct be an array element or a union member, where the storage comes
    // from somewhere else entirely.
    c += &format!(
        "ghost fn {sn}_claim_uninit (a: ptr) (#b: bytes)\n\
         \x20 requires mem_pts_to a 1.0R b\n\
         \x20 requires pure (len b == SizeT.v {sn}_sizeof)\n\
         \x20 ensures  {sn}_pts_to_uninit a\n\
         {{\n\
         {alloc}\
         \x20 fold {sn}_padding a 1.0R;\n\
         \x20 fold {sn}_pts_to_uninit a;\n}}\n\n",
        sn = sn,
        alloc = alloc
    );
    c += &format!(
        "fn {sn}_stack_alloc ()\n\
         \x20 returns a : ptr\n\
         \x20 ensures {sn}_pts_to_uninit a\n\
         {{\n\
         \x20 let a = mem_stack_alloc {sn}_sizeof;\n\
         \x20 {sn}_claim_uninit a;\n\
         \x20 a\n}}\n\n",
        sn = sn
    );

    // Freeing runs the carve backwards. `mem_join a n` needs the two halves
    // adjacent, so the joins go left to right, which is the reverse of the
    // order the splits ran in.
    // As with the carve, each reveal is paired with the join that immediately
    // consumes it rather than revealing everything first: `mem_join` describes
    // its result as `append` of the two halves, so `n` reveals held at once is
    // the same quadratic context the splits had.
    let reveal_at = |f: &StructField, free: &mut String| match &f.shape {
        FieldShape::One { pn } => {
            *free += &format!(
                "  rewrite ({pn}_pts_to_uninit (a +! {sn}_offsetof_{f}))\n    as ({pn}_pts_to_uninit {off});\n",
                pn = pn,
                sn = sn,
                f = f.name,
                off = at(f.offset)
            );
            *free += &format!("  {}_reveal_uninit {};\n", pn, at(f.offset));
        }
        FieldShape::Flex { .. } => *free += NO_FLEX_STORAGE,
        FieldShape::Array { pn, esize, len } => {
            *free += &format!(
                "  rewrite (array_pts_to_uninit {pn}_repr {es} {n} (a +! {sn}_offsetof_{f}))\n    as (array_pts_to_uninit {pn}_repr {es} {n} {off});\n",
                pn = pn,
                es = esize,
                n = len,
                sn = sn,
                f = f.name,
                off = at(f.offset)
            );
            *free += &format!(
                "  array_reveal_all_uninit {}_repr {} {}sz {}sz;\n",
                pn,
                at(f.offset),
                esize,
                len
            );
        }
    };
    let mut free = String::new();
    free += &format!("  unfold {}_pts_to_uninit a;\n", sn);
    free += &format!("  unfold {}_padding a 1.0R;\n", sn);
    if let Some(f) = field_at(0) {
        reveal_at(f, &mut free);
    }
    for off in bounds.iter() {
        if let Some(f) = field_at(*off) {
            reveal_at(f, &mut free);
        }
        free += &format!("  mem_join a {}sz;\n", off);
    }
    c += &format!(
        "ghost fn {sn}_reveal_uninit (a: ptr)\n\
         \x20 requires {sn}_pts_to_uninit a\n\
         \x20 ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SizeT.v {sn}_sizeof)\n\
         {{\n{free}}}\n\n",
        sn = sn,
        free = free
    );
    c += &format!(
        "fn {sn}_stack_free (a: ptr)\n\
         \x20 requires {sn}_pts_to_uninit a\n\
         {{\n  {sn}_reveal_uninit a;\n  mem_stack_free a;\n}}\n\n",
        sn = sn
    );

    // Going from a live struct back to storage is per field: the padding is
    // already in both predicates and passes straight through.
    let mut forget = String::new();
    forget += &format!("  unfold {}_pts_to a 1.0R x;\n", sn);
    for f in &si.fields {
        match &f.shape {
            FieldShape::One { pn } => {
                forget += &format!("  {}_forget (a +! {}_offsetof_{});\n", pn, sn, f.name);
            }
            FieldShape::Flex { .. } => forget += NO_FLEX_STORAGE,
            FieldShape::Array { pn, esize, len } => {
                forget += &format!(
                    "  array_forget_all {}_repr (a +! {}_offsetof_{}) {}sz {}sz;\n",
                    pn, sn, f.name, esize, len
                );
            }
        }
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
        match &f.shape {
            FieldShape::One { pn } => {
                write += &format!(
                    "  {}_write_uninit (a +! {}_offsetof_{}) x.fld_{};\n",
                    pn, sn, f.name, f.name
                );
            }
            FieldShape::Flex { .. } => write += NO_FLEX_STORAGE,
            FieldShape::Array { pn, esize, len } => {
                write += &format!(
                    "  {}_fill (a +! {}_offsetof_{}) x.fld_{};\n",
                    fill_name(pn, *esize, *len),
                    sn,
                    f.name,
                    f.name
                );
            }
        }
    }
    c += &format!(
        "fn {sn}_write_uninit (a: ptr) (x: {sn})\n\
         \x20 requires {sn}_pts_to_uninit a\n\
         \x20 ensures  {sn}_pts_to a 1.0R x\n\
         {{\n{write}  fold {sn}_pts_to a 1.0R x;\n}}\n\n",
        sn = sn,
        write = write
    );

    // Overwriting a whole structure that already holds a value. Going through
    // `_forget` rather than writing the fields in place is not a detour: both
    // need the full permission, and this way the padding is handled in exactly
    // one place instead of two.
    // Reading a whole structure is reading every field and packing the
    // record. It exists because a structure passed or returned by value is a
    // value in F* and an object in C, and the two have to meet somewhere.
    let mut read = String::new();
    for f in &si.fields {
        let reader = match &f.shape {
            FieldShape::One { pn } => format!("{}_read", pn),
            FieldShape::Array { pn, esize, len } => {
                format!("{}_read", fill_name(pn, *esize, *len))
            }
            FieldShape::Flex { .. } => NO_FLEX_STORAGE.to_string(),
        };
        read += &format!("  {}_focus_{} a;\n", sn, f.name);
        read += &format!(
            "  let v_{f} = {rd} (a +! {sn}_offsetof_{f});\n",
            f = f.name,
            rd = reader,
            sn = sn
        );
        read += &format!("  {}_unfocus_read_{} a;\n", sn, f.name);
    }
    if si.has_read {
        c += &format!(
            "fn {sn}_read (a: ptr) (#p: perm) (#x: erased {sn})\n\
         \x20 preserves {sn}_pts_to a p x\n\
         \x20 returns  y : {sn}\n\
         \x20 ensures  pure (y == reveal x)\n\
         \x20 ensures  rewrites_to y (reveal x)\n\
         {{\n{read}  {{ {fields} }}\n}}\n\n",
            sn = sn,
            read = read,
            fields = si
                .fields
                .iter()
                .map(|f| format!("fld_{} = v_{}", f.name, f.name))
                .collect::<Vec<_>>()
                .join("; ")
        );
    }

    c += &format!(
        "fn {sn}_write (a: ptr) (x: {sn}) (#y: erased {sn})\n\
         \x20 requires {sn}_pts_to a 1.0R y\n\
         \x20 ensures  {sn}_pts_to a 1.0R x\n\
         {{\n  {sn}_forget a;\n  {sn}_write_uninit a x;\n}}\n\n",
        sn = sn
    );
    c
}

/// Whether a struct has the generated automatic-storage operations, which is
/// the same condition `emit_struct_storage` checks: every field needs an
/// uninitialised view.
fn storable_struct(tds: &Typedefs, ty: &Type) -> bool {
    let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(tds, ty).val else {
        return false;
    };
    match tds.structs.get(&*n.val) {
        Some(si) => si.fields.iter().all(|f| match &f.shape {
            FieldShape::One { .. } => has_repr(tds, &f.ty),
            FieldShape::Array { .. } => true,
            FieldShape::Flex { .. } => false,
        }),
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
        // `&g` is a closed term: a global's address is fixed for the whole run.
        ExprT::Ref(inner) => match &strip_vattr(inner).val {
            ExprT::Var(v) if tds.global_addrs.contains(&*v.val.to_string()) => {
                Some(format!("addr_var_{}", v.val))
            }
            _ => None,
        },
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
/// A constant array global's value, as an F\* sequence term, together with
/// its element type and length.
///
/// The initialiser reaches the IR already padded out to the declared length --
/// a string literal shorter than its array is filled with zeroes by then -- so
/// the value is just the elements, in order, as a list. A list rather than a
/// chain of `Seq.upd`s because the length then comes from `normalize_term`
/// instead of one subtyping step per element, which is what makes a large
/// table affordable at all.
fn const_array(tds: &Typedefs, ty: &Type, e: &Expr) -> Option<(String, u64, String)> {
    let TypeT::FixedArray(elem, n) = &peel(tds, ty).val else {
        return None;
    };
    let ExprT::ArrayInit { elems, .. } = &strip_vattr(e).val else {
        return None;
    };
    if elems.len() as u64 != *n {
        return None;
    }
    let fty = fstar_type(tds, elem)?;
    let mut vals = Vec::with_capacity(elems.len());
    for x in elems {
        vals.push(const_expr(tds, elem, x)?);
    }
    Some((
        fty,
        *n,
        format!("(const_seq_with_len [{}] {})", vals.join("; "), n),
    ))
}

/// A subscript's index when it is a constant, after the casts C wraps it in.
fn const_index(e: &ExprT) -> Option<u64> {
    match e {
        ExprT::IntLit(n, _) => u64::try_from(&**n).ok(),
        ExprT::Cast(inner, _) | ExprT::VAttr(_, inner) => const_index(&inner.val),
        _ => None,
    }
}

/// Whether a global is published with a value -- possibly an abstract one --
/// by its own module, so that naming it needs no ownership.
///
/// An enumerator is excluded: it has no storage and no module, and its value is
/// inlined wherever it appears.
fn global_has_value(tds: &Typedefs, gv: &GlobalVar) -> bool {
    gv.is_pure
        && !gv.is_enum_constant
        && !global_var_is_array(gv)
        && has_repr(tds, &gv.ty)
        && palow_name(tds, &gv.ty).is_some()
        && fstar_type(tds, &gv.ty).is_some()
}

/// The value of an immutable global, as an F* type and a term, when this file
/// can name it.
///
/// A global with no initialiser is not a gap: a tentative definition is
/// initialised as if by zero (C17 6.9.2p2), so its value is as settled as an
/// explicit one. `extern const T g;` is a different matter -- it is immutable,
/// but which value it is was decided in another translation unit, and Palow
/// emits one module per unit with nowhere to put the shared constant. Reading
/// one is refused rather than assumed.
fn global_const(tds: &Typedefs, gv: &GlobalVar) -> Option<(String, String)> {
    if gv.is_enum_constant || global_var_is_array(gv) || !gv.is_pure || gv.is_extern {
        return None;
    }
    if !has_repr(tds, &gv.ty) {
        return None;
    }
    let fty = fstar_type(tds, &gv.ty)?;
    let v = match &gv.init {
        Some(e) => const_expr(tds, &gv.ty, e)?,
        None => static_zero(tds, &gv.ty).ok()?,
    };
    Some((fty, v))
}

fn emit_globals(tds: &Typedefs, tu: &TranslationUnit) -> Vec<Chunk> {
    let mut chunks: Vec<Chunk> = Vec::new();
    for decl in &tu.decls {
        let gv = match &decl.val {
            DeclT::GlobalVar(g) => g,
            _ => continue,
        };
        if gv.is_enum_constant {
            continue;
        }
        let name = &gv.name.val;
        let mut out = String::new();
        // An array global is published as a sequence constant rather than as
        // an object. Nothing can write it -- that is what `_pure` says -- so a
        // subscript of it is `Seq.index`, with no ownership involved at all.
        if global_var_is_array(gv) {
            // Whether or not the elements are known, the object has an
            // address, and a contract that owns the array names it. Publishing
            // it unconditionally is what makes a mutable array global work at
            // all: its ownership is threaded by hand through `_live`, and the
            // address is the only thing the model needs from the declaration.
            out += &format!("assume val addr_var_{} : ptr\n", name);
            out += &format!(
                "assume val addr_var_{}_not_null : squash (not (is_null addr_var_{}))\n",
                name, name
            );
            if gv.is_pure && !gv.is_extern {
                if let Some((fty, n, term)) =
                    gv.init.as_ref().and_then(|e| const_array(tds, &gv.ty, e))
                {
                    // `_pulse_opaque_to_smt` on the source declaration is
                    // load-bearing here, not decoration: the value of a
                    // thousand-element array is a chain of a thousand
                    // `Seq.upd`s, and letting the solver unfold it is what
                    // that annotation exists to prevent. The length stays in
                    // the type either way, so a subscript is still bounded --
                    // only its value becomes something a tactic has to
                    // establish rather than SMT.
                    out += &format!(
                        "{}let var_{} : (s: Seq.seq {} {{ Seq.length s == {} }}) = {}\n\n",
                        if gv.opaque_to_smt {
                            "[@@\"opaque_to_smt\"]\n"
                        } else {
                            ""
                        },
                        name,
                        fty,
                        n,
                        term
                    );
                }
            }
            chunks.push(Chunk {
                module: format!("Global_{}", name),
                code: out,
                origin: origin_of(decl),
            });
            continue;
        }
        // The address is a `ptr` whatever the global's type is, so it is
        // published for every addressable global; only the value and the
        // permission that goes with it need a type the model covers.
        let typed = palow_name(tds, &gv.ty)
            .filter(|_| has_repr(tds, &gv.ty))
            .and_then(|pn| fstar_type(tds, &gv.ty).map(|fty| (pn, fty)));
        let value = global_const(tds, gv);
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
        if let Some((pn, fty)) = typed.filter(|_| global_has_value(tds, gv)) {
            // An immutable global whose initialiser is in this file has a value
            // this file can write down. One declared `extern` does not: which
            // value it is was decided in another translation unit. That is a
            // gap in knowledge, not in ownership -- the object is still
            // immutable, and still readable -- so the value is named and left
            // abstract rather than refused. A reader learns that every read
            // yields *the same* value, which is the whole content of `const`
            // at an unknown initialiser.
            match value {
                Some((_, v)) => out += &format!("let var_{} : {} = {}\n", name, fty, v),
                None => out += &format!("assume val var_{} : {}\n", name, fty),
            }
            // The permission is existentially quantified, so a client can read
            // through the address but can never gather a full one and write.
            out += &format!(
                "assume val acquire_var_{} : unit -> stt_ghost unit emp_inames emp\n  (fun _ -> exists* (p: perm). {}_pts_to addr_var_{} p var_{})\n",
                name, pn, name, name
            );
        }
        out += "
";
        chunks.push(Chunk {
            module: format!("Global_{}", name),
            code: format!(
                "(* An immutable global is an F* constant plus an address; a mutable one\n   is an address and nothing else, which is inert because no permission for\n   it can ever be derived. *)\n\n{}",
                out
            ),
            origin: origin_of(decl),
        });
    }
    chunks
}

/// The witness argument of an indirect call, written out as a tuple spine of
/// `n` holes.
///
/// Inference stops at the tuple itself: Pulse solves a hole standing for a
/// witness LEAF, but a hole standing for a whole tuple stays stuck, because
/// the projections the callee's contract applies to it (`fst (reveal ?w)`)
/// cannot reduce until the hole is a real `Mktuple`. Writing the spine --
/// which is all the emitter knows, and all that is missing -- turns one stuck
/// hole into `n` solvable ones. The leaves are still inferred: which values
/// the callee is being handed is what the ownership in the caller's context
/// says, and that is exactly what slprop matching reads off.
fn witness_holes(n: usize) -> String {
    match n {
        0 => "(hide ())".to_string(),
        1 => "_".to_string(),
        _ => format!("(hide ({}))", vec!["_"; n].join(", ")),
    }
}

/// What a C name is used for, once ownership has to be threaded through the
/// call graph: the variables a body mentions and the functions it calls.
///
/// A mutable global's ownership arrives in the contract, so a function's
/// contract has to name every global its body touches -- and every global its
/// callees touch, transitively, because the callee's own `requires` has to be
/// satisfied from what the caller holds. C says none of this out loud, so it
/// is recovered by walking the body.
#[derive(Default)]
struct Touched {
    vars: HashSet<String>,
    calls: HashSet<String>,
    /// The functions whose address is taken. Only these need a `__fp`
    /// wrapper, and emitting one for every function would be noise.
    refs: HashSet<String>,
    /// The objects some body may store into: the base of an assignment's
    /// left-hand side, of an increment, and of any address that escapes. A
    /// global nothing here can write is effectively immutable for the whole
    /// run, and owning it would be worse than publishing its value.
    written: HashSet<String>,
    /// How many times each name is *rebound*: assigned straight to the name,
    /// incremented, or has its own address taken. Writing *through* a name
    /// does not count. A place built only from names that are never rebound
    /// denotes the same object everywhere in the body.
    rebound: HashMap<String, usize>,
    /// The pointers that stand for a place rather than for storage, so that
    /// what a body does to `*q` is recorded against the place instead. Empty
    /// while `alias_map` is deciding what belongs here.
    aliases: HashMap<String, Rc<Expr>>,
    /// The globals a contract asks to hold, named in `_live(g)`.
    lived: HashSet<String>,
    /// The named objects whose own address the body takes. Each of them needs
    /// storage, wherever in the body the `&` happens to appear.
    addressed: HashSet<String>,
}

/// The variable an lvalue ultimately reaches through, if it is a named object.
fn lvalue_base(e: &Expr) -> Option<String> {
    match &e.val {
        ExprT::Var(v) => Some(v.val.to_string()),
        ExprT::Member(x, _) | ExprT::Index(x, _) | ExprT::VAttr(_, x) | ExprT::Cast(x, _) => {
            lvalue_base(x)
        }
        _ => None,
    }
}

/// The name an lvalue *is*, as opposed to the name it reaches through.
/// Two steps of a path within a slot, joined. Either may be empty, which is
/// how the slot itself is named.
fn join_path(a: &str, b: &str) -> String {
    match (a.is_empty(), b.is_empty()) {
        (true, _) => b.to_string(),
        (_, true) => a.to_string(),
        _ => format!("{}.{}", a, b),
    }
}

/// The variable a code pointer is reached from: itself, or the object whose
/// field holds it. A contract grants validity by naming a parameter, and a
/// dispatch table is that parameter's fields, so both lead back to one name.
fn fp_base(e: &Expr) -> Option<String> {
    match &strip_vattr(e).val {
        ExprT::Var(v) => Some(v.val.to_string()),
        ExprT::Member(b, _) | ExprT::Deref(b) => fp_base(b),
        _ => None,
    }
}

fn lvalue_name(e: &Expr) -> Option<String> {
    match &e.val {
        ExprT::Var(v) => Some(v.val.to_string()),
        ExprT::VAttr(_, x) => lvalue_name(x),
        _ => None,
    }
}

fn touch_write(e: &Expr, t: &mut Touched) {
    if let Some(p) = alias_of(e, t) {
        touch_write(&p, t);
        return;
    }
    if let Some(b) = lvalue_base(e) {
        t.written.insert(b);
    }
    if let Some(n) = lvalue_name(e) {
        *t.rebound.entry(n).or_insert(0) += 1;
    }
}

/// The place an expression denotes through an alias: `*q`, and also `q` on its
/// own, whose value may be stored through wherever it ends up.
fn alias_of(e: &Expr, t: &Touched) -> Option<Rc<Expr>> {
    if t.aliases.is_empty() {
        return None;
    }
    let inner = match &strip_vattr(e).val {
        ExprT::Deref(x) => x,
        _ => e,
    };
    t.aliases.get(&lvalue_name(inner)?).cloned()
}

fn touch_expr(e: &Expr, t: &mut Touched) {
    if let Some(p) = alias_of(e, t) {
        touch_expr(&p, t);
        return;
    }
    let mut go = |x: &Rc<Expr>| touch_expr(x, t);
    match &e.val {
        ExprT::Var(v) => {
            t.vars.insert(v.val.to_string());
        }
        ExprT::FnCall(n, args) => {
            t.calls.insert(n.val.to_string());
            for a in args.iter() {
                touch_expr(a, t);
            }
        }
        ExprT::FnRef(n) => {
            t.calls.insert(n.val.to_string());
            t.refs.insert(n.val.to_string());
        }
        ExprT::FnPtrCall(f, args) => {
            touch_expr(f, t);
            for a in args.iter() {
                touch_expr(a, t);
            }
        }
        ExprT::Deref(x)
        | ExprT::Member(x, _)
        | ExprT::VAttr(_, x)
        | ExprT::UnOp(_, x)
        | ExprT::Cast(x, _)
        | ExprT::ContainerOf(x, _, _)
        | ExprT::Old(x)
        | ExprT::Forall(_, _, x)
        | ExprT::Exists(_, _, x)
        | ExprT::UnionInit(_, _, x)
        | ExprT::MallocArray(_, x)
        | ExprT::CallocArray(_, x)
        | ExprT::MallocFlex(_, x)
        | ExprT::CallocFlex(_, x)
        | ExprT::MemsetZero(_, x)
        | ExprT::Free(x) => go(x),
        ExprT::Live(x) => {
            if let ExprT::Var(v) = &strip_vattr(x).val {
                t.lived.insert(v.val.to_string());
            }
            touch_expr(x, t);
        }
        ExprT::PreIncr(x) | ExprT::PostIncr(x) | ExprT::PreDecr(x) | ExprT::PostDecr(x) => {
            touch_write(x, t);
            touch_expr(x, t);
        }
        // An address that escapes may be stored through, so the object it
        // names counts as written.
        ExprT::Ref(x) => {
            if let Some(n) = lvalue_name(strip_vattr(x)) {
                t.addressed.insert(n);
            }
            touch_write(x, t);
            touch_expr(x, t);
        }
        ExprT::Index(x, y) | ExprT::BinOp(_, x, y) => {
            touch_expr(x, t);
            touch_expr(y, t);
        }
        ExprT::AssignExpr(x, y) => {
            touch_write(x, t);
            touch_expr(x, t);
            touch_expr(y, t);
        }
        ExprT::Cond(a, b, c) => {
            touch_expr(a, t);
            touch_expr(b, t);
            touch_expr(c, t);
        }
        ExprT::Memset(_, a, b, c) => {
            touch_expr(a, t);
            touch_expr(b, t);
            touch_expr(c, t);
        }
        ExprT::StructInit(_, fs) => {
            for (_, x) in fs {
                touch_expr(x, t);
            }
        }
        ExprT::ArrayInit { elems, .. } => {
            for x in elems {
                touch_expr(x, t);
            }
        }
        ExprT::BoolLit(_)
        | ExprT::IntLit(..)
        | ExprT::FloatLit(..)
        | ExprT::InlinePulse(..)
        | ExprT::Malloc(_)
        | ExprT::Calloc(_)
        | ExprT::SizeOf(_)
        | ExprT::AlignOf(_)
        | ExprT::Error(_) => {}
    }
}

/// The C objects a clause's spliced Pulse fragments name.
///
/// `touch_expr` deliberately looks past an `_inline_pulse`: a spliced fragment
/// is not C and reads and writes nothing in C's sense. But an ownership clause
/// speaks *about* C objects through its antiquotations, and which ones it
/// speaks about is exactly what decides whether the author or the generated
/// frame states them.
fn spliced_names(e: &Expr, out: &mut HashSet<String>) {
    match &strip_vattr(e).val {
        ExprT::InlinePulse(code, _) => {
            for tok in &code.tokens {
                // Only `$&(x)`. An rvalue antiquotation *reads* an object,
                // and a read still needs the frame to say what is there;
                // taking an object's address is what a clause does when it is
                // about to state that object's ownership itself.
                let InlinePulseToken::LValueAntiquot { expr: x, .. } = tok else {
                    continue;
                };
                let mut t = Touched::default();
                touch_expr(x, &mut t);
                out.extend(t.vars);
                out.extend(t.written);
            }
        }
        ExprT::Cast(inner, _) => spliced_names(inner, out),
        ExprT::FnCall(_, args) => {
            for a in args.iter() {
                spliced_names(a, out);
            }
        }
        _ => {}
    }
}

fn touch_exprs(es: &Exprs, t: &mut Touched) {
    for e in es.iter() {
        touch_expr(e, t);
    }
}

fn touch_stmts(ss: &Stmts, t: &mut Touched) {
    for s in ss.iter() {
        match &s.val {
            StmtT::Call(e) | StmtT::Assert(e) | StmtT::Return(Some(e)) => touch_expr(e, t),
            StmtT::Let(_, _, e) => touch_expr(e, t),
            StmtT::DeclStackArray { size, .. } => touch_expr(size, t),
            // The alias assignment itself stores nothing: the pointer is a
            // name, not an object, and the address it takes does not escape.
            StmtT::Assign(a, b)
                if lvalue_name(a).is_some_and(|n| t.aliases.contains_key(&n))
                    && matches!(&strip_vattr(b).val, ExprT::Ref(..)) => {}
            StmtT::Assign(a, b) => {
                touch_write(a, t);
                touch_expr(a, t);
                touch_expr(b, t);
            }
            StmtT::If {
                cond,
                then_branch,
                else_branch,
                ensures,
            } => {
                touch_expr(cond, t);
                touch_stmts(then_branch, t);
                touch_stmts(else_branch, t);
                touch_exprs(ensures, t);
            }
            StmtT::Match {
                scrutinee,
                branches,
                default_branch,
                ensures,
            } => {
                touch_expr(scrutinee, t);
                for br in branches.iter() {
                    touch_exprs(&br.patterns, t);
                    touch_stmts(&br.body, t);
                }
                touch_stmts(default_branch, t);
                touch_exprs(ensures, t);
            }
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => {
                touch_expr(cond, t);
                touch_exprs(inv, t);
                touch_exprs(requires, t);
                touch_exprs(ensures, t);
                touch_stmts(body, t);
            }
            StmtT::GotoBlock { body, ensures, .. } => {
                touch_stmts(body, t);
                touch_exprs(ensures, t);
            }
            StmtT::Label { ensures, .. } => touch_exprs(ensures, t),
            StmtT::Decl(..)
            | StmtT::Break
            | StmtT::Continue
            | StmtT::Return(None)
            | StmtT::GhostStmt(_)
            | StmtT::Goto(_)
            | StmtT::Error => {}
        }
    }
}

/// The mutable globals a translation unit has storage for, as slot templates.
///
/// An immutable global is published as a value and needs no ownership, so it
/// is not here; an enum constant is not an object at all; an array global has
/// no `_pts_to` yet. What is left is a global with a fixed address and a
/// byte-level representation, which is exactly a slot that was allocated
/// before the program started and is never released.
fn mutable_globals(tds: &Typedefs, tu: &TranslationUnit) -> HashMap<String, Slot> {
    let mut out = HashMap::new();
    for decl in &tu.decls {
        let DeclT::GlobalVar(gv) = &decl.val else {
            continue;
        };
        if gv.is_enum_constant {
            continue;
        }
        // An immutable global this file initialises is a constant; reading it
        // needs no ownership, and granting some would only be noise.
        if gv.is_pure
            && !gv.is_extern
            && gv
                .init
                .as_ref()
                .is_some_and(|e| const_expr(tds, &gv.ty, e).is_some())
        {
            continue;
        }
        // A global array's elements are not `option`s: static storage is
        // zero-initialised before the program starts, so every element already
        // holds a value, and a read of one needs nothing but the ownership.
        let slot = match global_array_object(gv) {
            // The extent is in the type when this file declares the array and
            // absent when another one sizes it (`extern T g[]`). Both are
            // arrays and both are owned the same way: the ownership is an
            // `array_pts_to` over a sequence either way, and all the extent
            // does is refine that sequence's length. Where it is missing a
            // contract that needs a bound states one, exactly as it must for
            // an `_array T *` parameter.
            Some((elem, n)) => {
                let (Some(pn), Some(esize), Some(ety)) = (
                    palow_name(tds, elem),
                    palow_sizeof(tds, elem),
                    fstar_type(tds, elem),
                ) else {
                    continue;
                };
                if !has_repr(tds, elem) {
                    continue;
                }
                Slot {
                    name: gv.name.val.to_string(),
                    addr: format!("addr_var_{}", gv.name.val),
                    palow_ty: pn,
                    fstar_ty: match n {
                        Some(n) => format!("(s: Seq.seq {} {{ Seq.length s == {} }})", ety, n),
                        None => format!("(Seq.seq {})", ety),
                    },
                    init: true,
                    array: Some((format!("{}sz", esize), false)),
                    global: true,
                    union_arm: None,
                    filling: None,
                    holds_fn: BTreeMap::new(),
                    scattered: BTreeSet::new(),
                }
            }
            None => {
                let (Some(pn), Some(fty)) = (palow_name(tds, &gv.ty), fstar_type(tds, &gv.ty))
                else {
                    continue;
                };
                // A struct needs no byte-level `_repr` here: a global is never
                // allocated or released, so its `_pts_to` is all that is used.
                let is_struct = pn
                    .strip_prefix("struct_")
                    .is_some_and(|n| tds.structs.contains_key(n));
                if !has_repr(tds, &gv.ty) && !is_struct {
                    continue;
                }
                Slot {
                    name: gv.name.val.to_string(),
                    addr: format!("addr_var_{}", gv.name.val),
                    palow_ty: pn,
                    fstar_ty: fty,
                    init: true,
                    array: None,
                    global: true,
                    union_arm: None,
                    filling: None,
                    holds_fn: BTreeMap::new(),
                    scattered: BTreeSet::new(),
                }
            }
        };
        out.insert(gv.name.val.to_string(), slot);
    }
    out
}

/// One function's place in the output: its generated text, and which other
/// functions in this file that text names.
struct FnItem<'a> {
    name: String,
    origin: Option<Origin>,
    code: String,
    uses: HashSet<String>,
    defn: Option<&'a FnDefn>,
    env: Env,
    sig: Option<FnSurface>,
    /// The `__fp` wrapper's text, which goes into a module of its own.
    fp: Option<String>,
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

pub fn emit_palow(
    tu: &TranslationUnit,
    splice_inline: bool,
    model_specific: bool,
) -> Vec<PalowModule> {
    let mut tds = Typedefs::new(tu, splice_inline, model_specific);
    let mut base = Env::new();
    for decl in &tu.decls {
        base.push_decl(decl);
    }
    let structs = collect_structs(tu, &mut tds, &base);
    let mut chunks: Vec<Chunk> = structs;
    chunks.extend(emit_globals(&tds, tu));

    // A `_type` is a hand-written F* type expression with a C name attached.
    // Nothing about it is the memory model's business -- it never describes
    // storage, only a value a specification talks about -- so it is passed
    // through, and its C name resolves to it wherever a type is wanted.
    for decl in &tu.decls {
        let DeclT::OpaqueTypeDecl(td) = &decl.val else {
            continue;
        };
        let text = match include_pulse(&tds, &td.code) {
            Ok(t) if splice_inline => {
                format!("unfold\nlet ty_{} : Type = {}\n\n", td.name.val, t.trim())
            }
            Ok(_) => format!(
                "(* `{}` is not an F* type: {} *)\n\n",
                td.name.val,
                tds.no_splice()
            ),
            Err(why) => format!("(* `{}` is not an F* type: {} *)\n\n", td.name.val, why),
        };
        chunks.push(Chunk {
            module: format!("Type_{}", td.name.val),
            code: text,
            origin: origin_of(decl),
        });
    }
    if !splice_inline {
        tds.opaque_types.clear();
    }

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
        if ld.is_impure {
            if let Some(f) = fstar_type(&tds, &ld.ret_type) {
                tds.impure_lets.insert(ld.name.val.to_string(), f);
            }
            if let [a] = &ld.params[..]
                && let Some(n) = &a.name
            {
                tds.impure_bodies.insert(
                    ld.name.val.to_string(),
                    (n.val.to_string(), ld.body.clone()),
                );
            }
        }
        let slprop = matches!(tds.resolve(&ld.ret_type).val, TypeT::SLProp);
        if slprop {
            tds.slprop_lets.insert(ld.name.val.to_string());
        }
        let text = match emit_let_decl(&tds, &env, ld) {
            Ok(t) => t,
            Err(why) => {
                tds.pure_fns.remove(&*ld.name.val.to_string());
                tds.slprop_lets.remove(&*ld.name.val.to_string());
                format!(
                    "(* `{}` is not an F* definition: {} *)\n\n",
                    ld.name.val, why
                )
            }
        };
        chunks.push(Chunk {
            module: format!("Let_{}", ld.name.val),
            code: text,
            origin: origin_of(decl),
        });
    }

    // Hand-written Pulse comes after the `_let`s rather than before them. An
    // include block is a module of the author's own definitions, and a ghost
    // helper written there is usually stated in terms of the same `_let` the
    // contracts use -- which means it has to be able to name it. Nothing in a
    // `_let` can name an include block's *definitions* except textually, so
    // putting the includes second costs nothing.
    for decl in &tu.decls {
        let DeclT::IncludeDecl(id) = &decl.val else {
            continue;
        };
        if !splice_inline {
            continue;
        }
        let text = match include_pulse(&tds, &id.code) {
            Ok(t) => format!("{}\n\n", t.trim_end()),
            Err(why) => format!("(* `{}` is not translated: {} *)\n\n", id.module_name, why),
        };
        chunks.push(Chunk {
            module: id.module_name.to_string(),
            code: text,
            origin: origin_of(decl),
        });
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
        let text = match emit_pure_fn(&tds, &env, fndecl, body) {
            Ok(t) => t,
            // Falling back to the Pulse `fn` keeps the function callable from
            // code even when it cannot be a term. Only a specification that
            // mentions it is lost.
            Err(why) => {
                tds.pure_fns.remove(&*fndecl.name.val.to_string());
                format!(
                    "(* `{}` is not an F* definition: {} *)\n\n",
                    fndecl.name.val, why
                )
            }
        };
        chunks.push(Chunk {
            module: format!("Func_{}", fndecl.name.val),
            code: text,
            origin: origin_of(decl),
        });
    }
    let tds = tds;

    // The whole callee map is built before any body is translated. What a call
    // may do depends only on the callee's *signature*, so nothing here needs
    // the callees' code -- and building it up front is what lets a body call a
    // function defined further down the file, which C allows and F* does not.
    // Which mutable globals each function's contract has to name. A body's own
    // mentions are only the start: calling a function that touches a global
    // means holding that global's ownership at the call, so the sets close
    // under the call graph. The fixpoint is over a finite set and only grows,
    // so it terminates; recursion is no obstacle because the answer is the
    // least fixed point.
    let mut globals = mutable_globals(&tds, tu);
    let mut grants: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut calls: HashMap<String, HashSet<String>> = HashMap::new();
    let mut touched: Vec<(String, Touched)> = Vec::new();
    let mut written: HashSet<String> = HashSet::new();
    let mut lived: HashSet<String> = HashSet::new();
    let mut decayed: HashSet<String> = HashSet::new();
    for decl in &tu.decls {
        let DeclT::FnDefn(d) = &decl.val else {
            continue;
        };
        let mut t = Touched {
            aliases: {
                let mut e = base.clone();
                e.push_fn_decl_args_for_body(&d.decl);
                alias_map(&d.body, &|x| ptr_base(&tds, &e, x))
            },
            ..Touched::default()
        };
        touch_stmts(&d.body, &mut t);
        touch_exprs(&d.decl.requires, &mut t);
        touch_exprs(&d.decl.ensures, &mut t);
        written.extend(t.written.iter().cloned());
        lived.extend(t.lived.iter().cloned());
        decayed.extend(t.refs.iter().cloned());
        touched.push((d.decl.name.val.to_string(), t));
    }
    // A function's address can also be written down in a global's initialiser,
    // where no body mentions it. That is in fact the interesting case -- a
    // dispatch table is a constant, and the whole point of a constant one is
    // that nothing has to store into it -- so a wrapper has to be emitted for
    // everything the initialisers name, not just for what the code decays.
    for decl in &tu.decls {
        let DeclT::GlobalVar(gv) = &decl.val else {
            continue;
        };
        if let Some(init) = &gv.init {
            let mut t = Touched::default();
            touch_expr(init, &mut t);
            decayed.extend(t.refs.iter().cloned());
        }
    }
    // A global nothing in this file can store through is immutable for the
    // whole run whatever its declaration says, and handing its ownership
    // around would only lose what its initialiser said. Publishing its value
    // is the better answer, and is what milestone 5 already does for a `const`
    // one; until an initialiser of any type can be published, such a global
    // stays as it was.
    //
    // Unless the source asked for the ownership. `_live(g)` is the author
    // saying that this function holds `g`, and the reasoning above assumed
    // there was something better to give them -- which there is not for a
    // global declared `extern` and never stored through here: the value is
    // decided in another unit, so publishing it says nothing, and dropping
    // the ownership leaves the contract naming an object with no contents.
    globals.retain(|n, _| written.contains(n) || lived.contains(n));
    for (name, t) in touched {
        grants.insert(
            name.clone(),
            t.vars
                .iter()
                .filter(|v| globals.contains_key(*v))
                .cloned()
                .collect(),
        );
        calls.insert(name, t.calls);
    }
    loop {
        let mut changed = false;
        for (f, cs) in &calls {
            let mut add: BTreeSet<String> = BTreeSet::new();
            for c in cs {
                if let Some(g) = grants.get(c) {
                    add.extend(g.iter().cloned());
                }
            }
            let own = grants.get_mut(f).unwrap();
            for g in add {
                changed |= own.insert(g);
            }
        }
        if !changed {
            break;
        }
    }

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
        let granted: Vec<Slot> = grants
            .get(&*fndecl.name.val.to_string())
            .into_iter()
            .flatten()
            .map(|g| globals[g].clone())
            .collect();
        let decay = decayed.contains(&*fndecl.name.val.to_string());
        let sig = match emit_fn(&tds, &env, fndecl, &granted, decay) {
            Ok(s) => s,
            Err(why) => {
                items.push(FnItem {
                    origin: origin_of(decl),
                    name: fndecl.name.val.to_string(),
                    code: format!("(* skipped {}: {} *)\n\n", fndecl.name.val, why),
                    uses: HashSet::new(),
                    defn: None,
                    env,
                    sig: None,
                    fp: None,
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
                simple: if !fndecl.args.iter().all(|a| {
                    matches!(
                        a.mode,
                        ParamMode::Regular
                            | ParamMode::Const
                            | ParamMode::Out
                            | ParamMode::Consumed
                    )
                }) {
                    Err("moves ownership across the call")
                } else if fndecl.args.iter().any(|a| refined(&tds, &a.ty)) && !sig.contract {
                    // A `_refine` on a parameter is part of the contract on
                    // both sides of the call. When the contract translated it
                    // is in the emitted specification like any other clause;
                    // when it did not, a caller would be proving against a
                    // specification weaker than the source's.
                    Err("takes a `_refine`d argument whose contract did not translate")
                } else {
                    Ok(())
                },
                void: matches!(tds.resolve(&fndecl.ret_type).val, TypeT::Void),
                contract: sig.contract,
                fp: sig.fp.is_some(),
                fp_wits: sig.fp_wits,
                outs: fndecl
                    .args
                    .iter()
                    .map(|a| a.mode == ParamMode::Out)
                    .collect(),
                plain_ptrs: fndecl.args.iter().map(|a| is_plain(&tds, &a.ty)).collect(),
                arr_args: fndecl
                    .args
                    .iter()
                    .map(|a| extent(&tds, &a.ty) == Some(Extent::Array))
                    .collect(),
                consumes: fndecl
                    .args
                    .iter()
                    .map(|a| a.mode == ParamMode::Consumed)
                    .collect(),
                allocated: sig.ret_block.clone(),
            },
        );
        items.push(FnItem {
            origin: origin_of(decl),
            name: fndecl.name.val.to_string(),
            code: String::new(),
            uses: HashSet::new(),
            defn,
            env,
            fp: sig.fp.clone(),
            sig: Some(sig),
        });
    }

    // Recursion has to be broken somewhere: F* would need `let rec`/`rec fn`
    // and a termination argument that C does not supply, so a call on a cycle
    // is refused and the rest of the body is kept. `forbidden` grows until the
    // call graph is acyclic, which it must reach because each round removes at
    // least one edge.
    let mut forbidden: HashMap<String, HashSet<String>> = HashMap::new();
    // Which functions are divergent is not known until their bodies are
    // translated, and a caller of a divergent function is divergent in turn,
    // so the set is reached by repeating the whole pass until it settles.
    let mut divergent_fns: HashSet<String> = HashSet::new();
    let order = loop {
        let mut found: HashSet<String> = HashSet::new();
        for it in &mut items {
            let Some(sig) = &it.sig else { continue };
            let empty = HashSet::new();
            let no = forbidden.get(&it.name).unwrap_or(&empty);
            let body = match it.defn {
                None => Err(EXTERNAL.to_string()),
                Some(d) => emit_body(&tds, it.env.clone(), d, sig, &callees, no, &divergent_fns),
            };
            if matches!(&body, Ok(b) if b.divergent) {
                found.insert(it.name.clone());
            }
            it.uses = sig.uses.clone();
            if let Ok(b) = &body {
                it.uses.extend(b.uses.iter().cloned());
            }
            // A module never opens itself, and a self-edge is not a cycle to
            // break where the `_decreases` has already broken it. Leaving it
            // in would make the sort report the same back edge every round
            // and forbid the very call the measure justifies.
            if sig.self_rec {
                it.uses.remove(&it.name);
            }
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
                // A declaration with no definition in this translation unit
                // is not a translation gap: there is no C here to translate,
                // and its contract is what the linker's other half promises.
                // It is assumed, in the same words the old emitter uses, and
                // counted apart from the bodies this translation could not
                // produce -- counting the two together would make the
                // coverage measurement say something it does not mean.
                Err(why) if why == EXTERNAL => {
                    out += "{\n  (* external: the contract is assumed *)\n  \
                            assume (pure False);\n  unreachable ()\n}\n\n";
                }
                Err(why) => {
                    out += &format!("{{\n  admit() (* body: {} *)\n}}\n\n", why);
                }
            }
            it.code = out;
        }
        let settled = found.is_subset(&divergent_fns);
        divergent_fns.extend(found);
        match toposort(&items) {
            Ok(o) if settled => break o,
            Ok(_) => {}
            Err(back) => {
                for (from, to) in back {
                    forbidden.entry(from).or_default().insert(to);
                }
            }
        }
    };
    for i in order {
        let name = items[i].name.clone();
        chunks.push(Chunk {
            module: format!("Func_{}", name),
            code: std::mem::take(&mut items[i].code),
            origin: items[i].origin.clone(),
        });
        // The wrapper gets a module of its own, next to the function it
        // wraps. It is emitted only for a function whose address is taken --
        // one per function would be noise, and the contract has to be written
        // out a second time to produce it -- so a caller that only calls the
        // function directly should not have to depend on it. The name is the
        // one PAL already uses, which lets a test spell a wrapper the same way
        // for both memory models.
        if let Some(fp) = items[i].fp.take() {
            chunks.push(Chunk {
                module: format!("Funcptr_{}", name),
                code: fp,
                origin: items[i].origin.clone(),
            });
        }
    }

    into_modules(chunks)
}

/// The `open`s every generated module needs whatever it contains: the Palow
/// model itself, and the F* integer modules the emitted names are spelled in.
const PREAMBLE: &str = "\n#lang-pulse\nopen Pulse\n\
open Pulse.Lib.C.Palow.Bytes\n\
open Pulse.Lib.C.Palow.Ptr\n\
open Pulse.Lib.C.Palow\n\
open Pulse.Lib.C.Palow.Scalar\n\
open Pulse.Lib.C.Palow.Float\n\
open Pulse.Lib.C.Palow.CTypes\n\
open Pulse.Lib.C.Palow.Machine\n\
open Pulse.Lib.C.Palow.Array\n\
open Pulse.Lib.C.Palow.ConstSeq\n\
open Pulse.Lib.C.Palow.Local\n\
open Pulse.Lib.C.Palow.Nullable\n\
open Pulse.Lib.C.Palow.Alloc\n\
open Pulse.Lib.C.Palow.FnPtr\n\
module Seq = FStar.Seq\n\
module Bits = Pulse.Lib.C.Palow.Bits\n\
module Int8 = FStar.Int8\n\
module Int16 = FStar.Int16\n\
module Int32 = FStar.Int32\n\
module Int64 = FStar.Int64\n\
module UInt8 = FStar.UInt8\n\
module UInt16 = FStar.UInt16\n\
module UInt32 = FStar.UInt32\n\
module UInt64 = FStar.UInt64\n\
module SizeT = FStar.SizeT\n\
module Float32 = FStar.Float32\n\
module Float64 = FStar.Float64\n\n";

/// The top-level names a chunk defines. F* has no way to ask this of a string,
/// so it is read off the generated text -- which is safe to do only because
/// the text is generated: every definition starts at column zero and every
/// continuation line is indented, which the emitter maintains anyway because
/// Pulse is indentation-sensitive.
fn defined_names(code: &str) -> Vec<String> {
    const MODIFIERS: &[&str] = &[
        "assume",
        "val",
        "let",
        "rec",
        "noeq",
        "unopteq",
        "type",
        "fn",
        "ghost",
        "atomic",
        "unobservable",
        "divergent",
        "inline_for_extraction",
        "unfold",
        "irreducible",
        "instance",
        "new",
        "and",
    ];
    let mut out = Vec::new();
    for line in code.lines() {
        if line.starts_with(char::is_whitespace) || line.is_empty() {
            continue;
        }
        // A definition always opens with one of the modifiers above. Spliced
        // Pulse is not indented the way generated code is, so a contract
        // clause can start in column zero: without this, `requires` would be
        // recorded as a name the module defines, and every module in the file
        // would then be made to open it.
        let mut words = line.split_whitespace();
        let mut saw_modifier = false;
        let name = loop {
            match words.next() {
                None => break None,
                Some(w) if MODIFIERS.contains(&w) => {
                    saw_modifier = true;
                    continue;
                }
                Some(w) => break Some(w),
            }
        };
        let Some(name) = name else { continue };
        if !saw_modifier {
            continue;
        }
        // `let x = e in` binds locally, however far left it is written. A
        // spliced definition's body runs down the left margin, so without
        // this its local names would be published as the module's.
        if words.clone().any(|w| w == "in") {
            continue;
        }
        let name: String = name
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
            .collect();
        if !name.is_empty() {
            out.push(name);
        }
    }
    out
}

/// Wrap each chunk in a module that opens exactly the earlier modules it
/// names. The edges only ever point backwards, so the result cannot have a
/// cycle -- which matters, because F* modules may not be mutually recursive
/// and C declarations, unlike F* ones, routinely refer to each other in an
/// order the file does not fix.
fn into_modules(chunks: Vec<Chunk>) -> Vec<PalowModule> {
    // A C name can produce more than one chunk -- a `_pure` function that did
    // not become an F* definition leaves a note behind and is then translated
    // again as a Pulse `fn` -- and both belong to the same module.
    let mut merged: Vec<Chunk> = Vec::new();
    for ch in chunks {
        match merged.iter_mut().find(|m| m.module == ch.module) {
            Some(m) => m.code += &ch.code,
            None => merged.push(ch),
        }
    }
    let chunks = merged;

    let mut owner: HashMap<String, String> = HashMap::new();
    // What each module already opens, so that opening it brings those along.
    // F* `open` is not transitive, and a record literal names its labels
    // without naming its type: `{ fld_lo = 1ul }` for a `struct pair` nested
    // inside a `struct pairs` mentions nothing the scan below can see. Taking
    // the closure is sound because these modules are one generated namespace.
    let mut deps: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut out: Vec<PalowModule> = Vec::new();
    for ch in chunks {
        let mut opens: BTreeSet<String> = BTreeSet::new();
        let mut word = String::new();
        for c in ch.code.chars().chain(std::iter::once(' ')) {
            if c.is_alphanumeric() || c == '_' || c == '\'' {
                word.push(c);
                continue;
            }
            if !word.is_empty() {
                if let Some(m) = owner.get(&word) {
                    if *m != ch.module {
                        opens.insert(m.clone());
                    }
                }
                word.clear();
            }
        }
        let mut queue: Vec<String> = opens.iter().cloned().collect();
        while let Some(m) = queue.pop() {
            for d in deps.get(&m).into_iter().flatten() {
                if *d != ch.module && opens.insert(d.clone()) {
                    queue.push(d.clone());
                }
            }
        }
        deps.insert(ch.module.clone(), opens.clone());

        let mut code = format!("module {}\n", ch.module);
        code += HEADER;
        code += PREAMBLE;
        for m in &opens {
            code += &format!("open {}\n", m);
        }
        if !opens.is_empty() {
            code += "\n";
        }
        code += &ch.code;
        for n in defined_names(&ch.code) {
            owner.insert(n, ch.module.clone());
        }
        out.push(PalowModule {
            module_name: ch.module,
            code,
            origin: ch.origin,
        });
    }
    out
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
    /// Where the storage is. A local's is a stack allocation bound to
    /// `loc_<name>`; a mutable global's is the fixed address `addr_var_<name>`
    /// the module assumes, which is why a global can be an ordinary slot.
    addr: String,
    palow_ty: String,
    /// The F* type of the value the slot holds. A loop invariant has to bind
    /// one existential per live slot, and the binder needs a type.
    fstar_ty: String,
    init: bool,
    /// Set when the slot is a fixed-size array local. Its ownership is an
    /// `array_pts_to` at the `maybe_repr` representation rather than a
    /// points-to, because its elements are written one at a time; the string
    /// is the element size as a `size_t` literal, and the flag says whether
    /// the elements are `option`s. A local's are: they are written one at a
    /// time. A global's are not, because static storage is zero-initialised
    /// before the program starts, so every element already holds a value.
    array: Option<(String, bool)>,
    /// Set when the slot is a mutable global. Its storage outlives the
    /// function, so the ownership arrives in the contract and must not be
    /// allocated on entry or released on exit.
    global: bool,
    /// Set when the slot is a union arm made live by `$activate`: the union's
    /// Palow name and the arm's. Filling the arm's last field completes a
    /// value of the arm's type, and it is the union that holds it, so the
    /// gather has to be followed by the arm's `unfocus`.
    union_arm: Option<(String, String)>,
    /// Set when the slot is an *array* arm made live by `$activate`: the arm's
    /// static length, and the element indices written so far. An array arm is
    /// storage until every element of it holds a value, and the write that
    /// completes it is the one that makes the union hold the arm again --
    /// which is the same bookkeeping a struct arm's fields get, indexed
    /// rather than named.
    filling: Option<(u64, BTreeSet<u64>)>,
    /// The C functions whose addresses were last stored in this slot, keyed
    /// by the path within it: the empty string for the slot itself, `op` for
    /// the field of that name, `inner.op` for a field of a field. A code
    /// pointer's *value* is an address, but what may be done with it is the
    /// separate `valid` fact, and nothing in the points-to carries that.
    /// Remembering the store is what lets an indirect call seed validity
    /// itself, instead of the source having to write a `_ghost_stmt` -- and a
    /// dispatch table is exactly a struct whose fields are code pointers, so
    /// the record has to be per-field rather than per-slot.
    holds_fn: BTreeMap<String, String>,
    /// The fields already written, while the slot holds a struct that is being
    /// built one field at a time. Empty means the slot is whole: either
    /// storage or a value, according to `init`. Non-empty means it is neither
    /// -- `_scatter_uninit` has run and `_gather` has not -- and the fields
    /// named here hold values while the rest is still storage.
    scattered: BTreeSet<String>,
}

impl Slot {
    /// What the slot owns, at a given value.
    fn pts_to(&self, value: &str) -> String {
        match &self.array {
            None => format!("{}_pts_to {} 1.0R {}", self.palow_ty, self.addr, value),
            Some((esize, maybe)) => format!(
                "array_pts_to {r} (SizeT.v {e}) {n} 1.0R {v}",
                r = self.elem_repr(esize, *maybe),
                e = esize,
                n = self.addr,
                v = value
            ),
        }
    }

    /// The representation the slot's elements are stored at.
    fn elem_repr(&self, esize: &str, maybe: bool) -> String {
        if maybe {
            format!("(maybe_repr {}_repr (SizeT.v {}))", self.palow_ty, esize)
        } else {
            format!("{}_repr", self.palow_ty)
        }
    }
}

/// One open field focus: where the field is, and how to close it again.
struct FieldFocus {
    /// The Palow name of the struct the field belongs to.
    sn: String,
    /// The field of the struct's value the access goes through. For a
    /// bit-field this is the storage unit it shares, not the bit-field
    /// itself, which has no storage to focus.
    field: String,
    /// Where the bit-field sits in that unit, when the access is to one.
    bits: Option<BitPos>,
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
    /// `zeroed` for `calloc`.
    fill: &'static str,
    /// For a `calloc`ed single object whose type says an all-zero range is a
    /// value: that value, and the lemma calls that say so. The block is then
    /// claimed as an initialised object rather than as raw storage, which is
    /// what lets C read it before writing it -- the one thing `calloc` gives
    /// that `malloc` does not.
    zero: Option<(String, Vec<String>)>,
    /// For a block a call handed over rather than an allocator: the slprop the
    /// nullness guard encloses, in the callee's own words. Such a block
    /// arrives already typed, so the nullness test spends the guard and stops
    /// there -- there is nothing left to claim.
    taken: Option<String>,
    /// Whether the null test has been passed. Until it has, the block is under
    /// `unless_null` and unusable.
    checked: bool,
    /// Whether the pointee has been written. `malloc` hands back uninitialised
    /// storage, so the first store through the pointer is an initialising one.
    init: bool,
    /// Whether `free` has already taken the block back.
    freed: bool,
    /// The fields written so far, while the block is in pieces -- the same
    /// bookkeeping a local struct gets, for the same reason: C fills a
    /// `malloc`ed object one field at a time, and the object only becomes a
    /// value again once every field has been written.
    scattered: BTreeSet<String>,
    /// For `malloc(sizeof(T) * n)`, what makes the block an array: the element
    /// count, the element size, and -- for `calloc` -- the value the zero bytes
    /// stand for at the element type.
    array: Option<ArrayBlock>,
}

/// Which piece of storage is currently in pieces: a local's slot, or an
/// allocated block.
#[derive(Clone, Copy)]
enum Scattering {
    Slot(usize),
    Block(usize),
}

/// The array shape of an allocated block.
#[derive(Clone)]
struct ArrayBlock {
    /// The element count, as a `SizeT.t` term.
    n: String,
    /// The element size, as a `SizeT.t` literal.
    esize: String,
    /// The whole block's size in bytes, as a `SizeT.t` term.
    nbytes: String,
    /// The element value an all-zero range represents, when the allocator
    /// promised zeros and the element type has such a value, together with the
    /// lemma calls that say so.
    zero: Option<(String, Vec<String>)>,
    /// Whether the block has been claimed into the *initialised* view. A
    /// `calloc`ed extent starts in the uninitialised one -- every cell a
    /// `Some`, but a `Some` all the same -- and a callee that takes an
    /// ordinary array wants the other view. Which one it is in decides how it
    /// is given back.
    filled: bool,
}

/// What one arm of an `if` produced: its statements, and the state it leaves
/// the enclosing scope in.
struct BranchResult {
    lines: Vec<String>,
    inits: Vec<bool>,
    /// Which function each enclosing slot is known to hold on this path.
    holds: Vec<BTreeMap<String, String>>,
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
    /// Whether a `__fp` wrapper was emitted, so the function can be decayed
    /// to a code pointer.
    fp: bool,
    /// How many components that wrapper's witness tuple has.
    fp_wits: usize,
    /// Which parameters are `_out`, by position. Those arguments are not
    /// evaluated: what is passed is storage, not a value.
    outs: Vec<bool>,
    /// Which parameters are `_plain`, by position. A literal has no ownership
    /// to give, so its address may only be passed to one of these.
    plain_ptrs: Vec<bool>,
    /// Which parameters are `_array`s, and so want a whole sequence's
    /// ownership rather than a single pointee's.
    arr_args: Vec<bool>,
    /// Which parameters are `_consumes`, by position. The argument's ownership
    /// does not come back, so the caller stops accounting for it.
    consumes: Vec<bool>,
    /// What the call hands the caller, when the return type grants a block.
    /// The caller has to start tracking it or the ownership the `ensures` just
    /// granted would be left over.
    allocated: Option<RetBlock>,
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
    /// This function's own name, when the signature is `fn rec`. A call to it
    /// is not a cycle to break but the recursion the `_decreases` justifies.
    self_rec: Option<String>,
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
    /// Variables bound by a quantifier in an assertion. They have no storage,
    /// so they resolve to their own name rather than through a slot.
    spec_binders: HashMap<String, String>,
    /// The name the returned value is bound to while the ghost statements that
    /// follow a `return` are translated. `$(return)` is how such a statement
    /// names the value it is there to say something about, and it only has a
    /// name at all because those statements exist.
    ret_binding: Option<String>,
    /// Array-kind pointer parameters, by C name.
    arrays: HashMap<String, ArrayParam>,
    /// `_out` array parameters and the term for the cells handed in; see
    /// `FnSurface::olens`.
    olens: HashMap<String, String>,
    /// The function's parameters, by C name. Ownership of what a pointer points
    /// to is granted by the contract, and the contract only names parameters.
    params: HashSet<String>,
    /// Whether the emitted precondition carries any pure fact. Bounds and
    /// overflow obligations are discharged by those, so without one there is
    /// nothing to discharge them with. A `_refine` on a parameter's type
    /// counts: the fact reaches the body the same way whoever wrote it down.
    requires_ok: bool,
    /// The ownership the contract grants over the parameters' pointees, which
    /// a loop invariant has to restate.
    owned: &'a [OwnedParam],
    /// Parameters whose pointee the emitted contract owns; see `FnSurface`.
    granted: &'a HashSet<String>,
    /// See `FnSurface::spliced_own`.
    spliced_own: bool,
    /// Parameters whose ownership sits behind a nullness guard, so a loop
    /// invariant claiming their storage is claiming the guard is discharged.
    guarded: &'a HashSet<String>,
    /// Parameters the contract hands an `is_valid` for, and so the only
    /// pointers this body may call through without knowing the target.
    valid_fps: &'a HashSet<String>,
    /// Locals whose validity an `_ensures` on an `if` established. The
    /// signature's `valid_fps` says which *parameters* the contract spoke for;
    /// this says which locals the body's own annotations did.
    local_valid_fps: HashSet<String>,
    /// Consumed `_allocated` parameters and the Palow name of what they point
    /// at. See `FnSurface::freeables`.
    freeables: &'a HashMap<String, String>,
    /// Which of those this body has already returned to the allocator.
    consumed_freed: HashSet<String>,
    /// Parameters whose ownership does not come back. See `FnSurface`.
    consumed: &'a HashSet<String>,
    /// Addresses whose validity this body has seeded and not yet put down,
    /// with the pre and post it was seeded at. Both are needed to put it down
    /// again: a contract may hold a second, weaker validity for the same
    /// address, and `_` would let Pulse pick that one instead.
    seeded: Vec<(String, String, String, String)>,
    /// The functions whose seeded validity has since been handed to a call
    /// inside an aggregate. What comes back is the same fact, but stated at
    /// the value the callee's postcondition binds, so the term that was
    /// seeded is no longer the term to put down.
    laundered: HashSet<String>,
    /// The functions whose validity this function's `ensures` hands on. One of
    /// these is not the body's to put down on the way out.
    post_valid: &'a HashSet<String>,
    /// Whether the return's ownership is spliced; see `FnSurface`.
    ret_spliced: bool,
    /// The labels in scope, innermost last, each with the statements that run
    /// when control reaches it. A `goto` is translated by translating its
    /// label's continuation there and then: Pulse has no jump, and every path
    /// to a label has to be typed on its own anyway.
    gotos: Vec<(String, Vec<Rc<Stmt>>, Rc<Exprs>)>,
    /// Whether a loop encloses the statement being translated, so `break` and
    /// `continue` have something to leave.
    in_loop: bool,
    /// Ghost steps owed at the end of the current statement. A local array
    /// handed to a callee is converted to the view the callee asks for and
    /// back again, and the way back cannot be emitted until the call has been.
    pending_close: Vec<String>,
    /// Array elements opened by `$unfold-uninit` and not yet closed, as the
    /// element's address and the steps that put it back. An element whose
    /// fields are written one statement at a time cannot be closed between
    /// them -- there is no value to put back until the last field is written
    /// -- so the open has to outlive the statement that made it. The author
    /// says where it ends, with the matching `$fold`.
    open_elems: Vec<(String, Vec<String>)>,
    /// Parameters whose `_own` is currently unfolded. Deep ownership is held
    /// folded, because that is the form a contract states and a call passes;
    /// a statement that reaches through a pointer field scatters it, uses the
    /// pieces, and gathers them back before the statement ends. Bracketing it
    /// per statement rather than per function is what keeps every branch,
    /// loop and call seeing the same shape.
    own_open: Vec<(String, String)>,
    /// How many slots existed when the enclosing loop's body began. A `break`
    /// or `continue` past a slot allocated since then would skip its release.
    loop_mark: Option<usize>,
    /// Functions already known to be divergent. Calling one makes this body
    /// divergent too, which is why the whole set is reached by a fixpoint
    /// rather than in one pass.
    divergent_fns: &'a HashSet<String>,
    /// Whether any parameter is `_out`. Such a parameter's storage is
    /// uninitialised on entry and initialised by the body, so it is not a
    /// fixed part of the frame a loop invariant can restate.
    has_out: bool,
    /// Set by a loop: the function has to be declared `divergent`, since PAL
    /// translates no `decreases` measure.
    divergent: bool,
    /// Heap blocks held in locals, in allocation order.
    blocks: Vec<Block>,
    /// Local pointers that stand for a place rather than for storage. See
    /// `alias_map`.
    aliases: HashMap<String, Rc<Expr>>,
    /// Local pointers loaded once out of memory, with what they were loaded
    /// from. See `ptr_source_map`.
    ptr_src: HashMap<String, Rc<Expr>>,
    /// Locals that are another name for an array: `T *p = a;`. A subscript of
    /// one is a subscript of the array it names. See `array_alias_map`.
    array_aliases: HashMap<String, String>,
    /// Which member of a union at a given address is live, where the emitter
    /// knows. C's rule is that reading a member other than the one last
    /// written is not reading what you wrote, and Palow says the same thing by
    /// construction: the value of a union is tagged, and `union_X_focus_m`
    /// only applies when the tag is `m`. So a read is translatable exactly
    /// when a write to that member came first and nothing since could have
    /// changed it. Keyed by the address expression, which is the emitter's own
    /// name for the object.
    active: HashMap<String, String>,
    /// Union members the function's own `_requires` says are the live ones,
    /// as the C lvalue naming the union object and the member's name. A read
    /// of a union member is only sound where the member is the live one, and
    /// the contract is the other place besides a write in this body where
    /// that can be known.
    live_arms: Vec<(Rc<Expr>, String)>,
}

/// What a subscript through an array parameter needs: the element's Palow type
/// name, and its size as a `size_t` literal.
struct ArrayParam {
    pn: String,
    esize: String,
    /// The term for the array's base address.
    addr: String,
    /// Whether the elements are `option`s. A parameter's are not -- the caller
    /// has already initialised them -- but a heap block's initialisation is
    /// tracked element by element, so its are.
    maybe: bool,
    /// Whether the length is settled here. An array *parameter*'s is whatever
    /// the caller passed, so a subscript's bounds obligation can only come from
    /// the function's own `_requires`; a block allocated in this body has the
    /// length written into the sequence it was claimed at.
    known_len: bool,
}

/// Whether a `break` in this statement list leaves *this* loop. A nested
/// loop catches its own, so the search stops there.
fn has_break(body: &Stmts) -> bool {
    fn in_stmt(s: &Stmt) -> bool {
        match &s.val {
            StmtT::Break => true,
            StmtT::While { .. } => false,
            StmtT::If {
                then_branch,
                else_branch,
                ..
            } => has_break(then_branch) || has_break(else_branch),
            StmtT::Match {
                branches,
                default_branch,
                ..
            } => branches.iter().any(|b| has_break(&b.body)) || has_break(default_branch),
            StmtT::GotoBlock { body, .. } => has_break(body),
            _ => false,
        }
    }
    body.iter().any(|s| in_stmt(s))
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

    /// Make a union arm the live one, leaving its storage uninitialised.
    ///
    /// C says the member you last wrote is the one you may read, and the
    /// emitter usually sees that write. It cannot when the write fills the
    /// arm a *sub-field* at a time: there is no point at which the arm is a
    /// value, so there is no store to see. `$activate` is the author saying
    /// so, and Palow spells it `switch`: the union's value is given up and
    /// the arm's storage handed back, to be filled field by field from here.
    fn activate_arm(&mut self, ty: &Type, arm: &Ident, obj: &Expr) -> Result<(), String> {
        let TypeT::TypeRef(TypeRefKind::Union(uname)) = &peel(self.tds, ty).val else {
            return Err("`$activate` of something that is not a union".to_string());
        };
        let un = format!("union_{}", uname.val);
        let Some(ui) = self.tds.unions.get(&*uname.val.to_string()) else {
            return Err(format!(
                "`$activate` of union {}, which has no Palow type",
                uname.val
            ));
        };
        let Some(m) = ui.members.iter().find(|m| m.name == *arm.val.to_string()) else {
            return Err(format!(
                "`$activate` of `{}`, which is not a member",
                arm.val
            ));
        };
        // `$activate` names the union through a pointer to it, so the
        // address is the pointer's value.
        let a = self.inline(obj)?;
        // Storage that has never held a value switches from the storage view
        // rather than from a value, exactly as a whole-member write does.
        let from_uninit = self
            .slots
            .iter()
            .rposition(|s| s.addr == a && !s.init)
            .is_some()
            || self
                .blocks
                .iter()
                .any(|b| b.tmp == a && b.checked && !b.freed && !b.init);
        self.lines.push(format!(
            "{}_switch{}_{} {};",
            un,
            if from_uninit { "_uninit" } else { "" },
            arm.val,
            a
        ));
        self.active.insert(a.clone(), arm.val.to_string());
        // An array arm has no single Palow name -- its ownership is the array
        // combinator applied to its element's -- so it gets a slot of the same
        // shape a local array has: storage whose cells are `option`s, written
        // one at a time. The switch hands it over folded, with the length
        // pinned in the slprop; every access wants it unfolded, which is the
        // form the elements are focused out of.
        if let Some(FieldShape::Array { pn, esize, len }) = field_shape(self.tds, &m.ty) {
            let TypeT::FixedArray(elem, _) = &peel(self.tds, &m.ty).val else {
                return Err(format!(
                    "`$activate` of member `{}`, which is not a fixed-size array",
                    arm.val
                ));
            };
            let Some(ety) = fstar_type(self.tds, elem) else {
                return Err(format!(
                    "`$activate` of member `{}`, whose elements have no Palow type",
                    arm.val
                ));
            };
            self.lines.push(format!(
                "unfold array_pts_to_uninit {}_repr {} {} {};",
                pn, esize, len, a
            ));
            self.slots.retain(|s| s.addr != a);
            self.slots.push(Slot {
                name: format!("*{}.{}", a, arm.val),
                addr: a,
                palow_ty: pn,
                fstar_ty: ety,
                init: false,
                array: Some((format!("{}sz", esize), true)),
                global: true,
                union_arm: Some((un, arm.val.to_string())),
                holds_fn: BTreeMap::new(),
                scattered: BTreeSet::new(),
                filling: Some((len, BTreeSet::new())),
            });
            return Ok(());
        }
        let (Some(pn), Some(fty)) = (palow_name(self.tds, &m.ty), fstar_type(self.tds, &m.ty))
        else {
            return Err(format!(
                "`$activate` of member `{}`, which has no Palow type",
                arm.val
            ));
        };
        // The arm's storage is now what is held at that address, and it is
        // uninitialised. Anything already recorded there described the union
        // and no longer does.
        self.slots.retain(|s| s.addr != a);
        self.slots.push(Slot {
            name: format!("*{}.{}", a, arm.val),
            addr: a,
            palow_ty: pn,
            fstar_ty: fty,
            init: false,
            array: None,
            // The union's own storage is released by whoever owns it; this
            // slot only records what is in it.
            global: true,
            union_arm: Some((un, arm.val.to_string())),
            holds_fn: BTreeMap::new(),
            scattered: BTreeSet::new(),
            filling: None,
        });
        Ok(())
    }

    /// Close whichever array element a `$fold` ends the bracket of. The most
    /// recent open is the one it closes: the brackets nest.
    fn close_open_elem(&mut self, _code: &InlinePulseCode) {
        let Some((at, close)) = self.open_elems.pop() else {
            return;
        };
        self.lines.extend(close);
        self.slots.retain(|s| s.addr != at);
    }

    /// Record that a pointed-to struct is storage this body owns whose
    /// contents are not yet valid.
    ///
    /// This is the same slot an `_out` parameter gets: the address is a
    /// value the body already has rather than a stack allocation, the field
    /// writes scatter into it and the last one gathers it back up, and
    /// nothing here frees it. Saying nothing is always safe -- a body that
    /// then writes a field will simply fail to find the ownership and be
    /// admitted with a reason -- so every step below just gives up quietly.
    fn note_uninit(&mut self, e: &Expr) {
        let Ok(ty) = self.ty_of(e) else { return };
        let TypeT::Pointer(pt, _) = &peel(self.tds, &ty).val else {
            return;
        };
        let (Some(pn), Some(fty)) = (palow_name(self.tds, pt), fstar_type(self.tds, pt)) else {
            return;
        };
        if !storable_struct(self.tds, pt) {
            return;
        }
        // Naming the address must cost nothing: this is bookkeeping, not an
        // access. An address that takes steps to reach -- an array element,
        // say -- is one the access through it will reach for itself, so the
        // steps are rolled back and the note is dropped.
        // `$unfold-uninit($(p))` where `p` names an array element. The
        // element has to be focused out of the array to be addressed at all,
        // and -- unlike every other access -- that focus has to outlive the
        // statement, because the fields are written one statement at a time
        // and there is no value to put back until the last of them. So the
        // open is emitted here and the close is owed to the matching `$fold`.
        let deref = ExprT::Deref(Rc::new(e.clone())).with_loc(e.loc.clone()) as Rc<Expr>;
        if let Some(pl) = self.unalias(&deref)
            && let ExprT::Index(base, idx) = &strip_vattr(&pl).val
            && self.is_array_place(base)
        {
            let (base, idx) = (base.clone(), idx.clone());
            let mark = self.lines.len();
            let Ok(f) = self.focus_elem(&base, Some(&idx), false) else {
                self.lines.truncate(mark);
                return;
            };
            if self.slots.iter().any(|s| s.addr == f.at) {
                self.lines.truncate(mark);
                return;
            }
            self.lines.extend(f.open_write.iter().cloned());
            self.open_elems.push((f.at.clone(), f.close_write.clone()));
            self.slots.push(Slot {
                name: format!("*{}", f.at),
                addr: f.at,
                palow_ty: pn,
                fstar_ty: fty,
                init: false,
                array: None,
                global: true,
                union_arm: None,
                filling: None,
                holds_fn: BTreeMap::new(),
                scattered: BTreeSet::new(),
            });
            return;
        }
        let mark = self.lines.len();
        let closing = self.pending_close.len();
        let mut rollback = |me: &mut Self| {
            me.lines.truncate(mark);
            me.pending_close.truncate(closing);
        };
        let Ok(addr) = self.inline(e) else {
            rollback(self);
            return;
        };
        if self.lines.len() != mark || self.pending_close.len() != closing {
            rollback(self);
            return;
        }
        if self.slots.iter().any(|s| s.addr == addr) {
            return;
        }
        self.slots.push(Slot {
            name: format!("*{}", addr),
            addr,
            palow_ty: pn,
            fstar_ty: fty,
            init: false,
            array: None,
            global: true,
            union_arm: None,
            filling: None,
            holds_fn: BTreeMap::new(),
            scattered: BTreeSet::new(),
        });
    }

    /// Whether a global has a value published as an F* constant: it is
    /// immutable, this file initialises it, and the initialiser is a literal.
    /// Whether `v` names an array global this file published as a sequence
    /// constant, in which case a subscript of it needs no ownership.
    fn global_array_value(&self, v: &Ident) -> bool {
        match self.env.lookup_global_var(v) {
            Some(gv) => {
                global_var_is_array(gv)
                    && gv.is_pure
                    && !gv.is_extern
                    && gv
                        .init
                        .as_ref()
                        .is_some_and(|e| const_array(self.tds, &gv.ty, e).is_some())
            }
            None => false,
        }
    }

    /// The constant an lvalue reads, when it is rooted at a global nothing in
    /// the program can write. Returns the type at that path together with the
    /// initialiser that reached it; `None` means the path is covered by
    /// zero-initialisation, which is what a partial initialiser leaves behind
    /// and what a tentative definition is made of.
    ///
    /// This is the general form of the array case: `entry_packets.desc[0]` and
    /// `global_partial.initialized` are settled at translation time for the
    /// same reason `padded[0]` is, and walking the path is all it takes.
    fn const_path(&self, e: &Expr) -> Option<(Rc<Type>, Option<Rc<Expr>>)> {
        // A pointer that is another name for a place reaches the same
        // constant, and reading a global through its address is the usual way
        // C code reaches one.
        if let Some(q) = self.unalias(e) {
            return self.const_path(&q);
        }
        match &strip_vattr(e).val {
            ExprT::Var(v) => {
                if self.slots.iter().any(|s| s.name == *v.val) {
                    return None;
                }
                let gv = self.env.lookup_global_var(v)?;
                if gv.is_enum_constant || !gv.is_pure || gv.is_extern {
                    return None;
                }
                Some((gv.ty.clone(), gv.init.clone()))
            }
            ExprT::Member(base, f) => {
                let (ty, init) = self.const_path(base)?;
                // A union initialiser names exactly one member, and reading
                // any other one is not a constant read: the bytes are there,
                // but what they mean at that type is a reinterpretation the
                // initialiser did not decide.
                if let TypeT::TypeRef(TypeRefKind::Union(n)) = &peel(self.tds, &ty).val {
                    let fty =
                        self.env
                            .lookup_union(n)?
                            .fields
                            .iter()
                            .find_map(|x| match &x.val {
                                FieldT::Plain { name, ty } if *name.val == *f.val => {
                                    Some(ty.clone())
                                }
                                _ => None,
                            })?;
                    let at = match init.as_ref().map(|x| &strip_vattr(x).val) {
                        Some(ExprT::UnionInit(_, m, x)) if *m.val == *f.val => Some(x.clone()),
                        _ => return None,
                    };
                    return Some((fty, at));
                }
                let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(self.tds, &ty).val else {
                    return None;
                };
                let fty = self
                    .tds
                    .structs
                    .get(&*n.val)?
                    .fields
                    .iter()
                    .find(|x| *x.name == *f.val.to_string())?
                    .ty
                    .clone();
                let at = match init.as_ref().map(|x| &strip_vattr(x).val) {
                    Some(ExprT::StructInit(_, inits)) => inits
                        .iter()
                        .find(|(n, _)| *n.val == *f.val)
                        .map(|(_, x)| x.clone()),
                    // A field the initialiser does not name is zero, and so is
                    // every field of a global with no initialiser at all.
                    None => None,
                    _ => return None,
                };
                Some((fty, at))
            }
            ExprT::Index(base, idx) => {
                let (ty, init) = self.const_path(base)?;
                let TypeT::FixedArray(elem, n) = &peel(self.tds, &ty).val else {
                    return None;
                };
                // An array the initialiser never reached is zero at every
                // index, so which index it is does not have to be known. That
                // is the only case where a symbolic subscript reads as a
                // constant, and it is the common one: a static aggregate with
                // no initialiser at all.
                if init.is_none() {
                    return Some((elem.clone(), None));
                }
                let k = const_index(&strip_vattr(idx).val)?;
                if k >= *n {
                    return None;
                }
                let at = match init.as_ref().map(|x| &strip_vattr(x).val) {
                    Some(ExprT::ArrayInit { elems, .. }) => {
                        Some(elems.get(usize::try_from(k).ok()?)?.clone())
                    }
                    None => None,
                    _ => return None,
                };
                Some((elem.clone(), at))
            }
            _ => None,
        }
    }

    /// The constant an lvalue reads, as an F\* term, when there is one. Only a
    /// scalar qualifies: an aggregate has no literal to fold to, and falls
    /// through to the ordinary access.
    fn const_read(&self, e: &Expr) -> Option<String> {
        let (ty, init) = self.const_path(e)?;
        match init {
            Some(x) => const_expr(self.tds, &ty, &x),
            // What an initialiser did not reach is not all-bits-zero but the
            // static initialisation of C11 6.7.9p10: an arithmetic member is
            // zero and a pointer member is a null pointer.
            None => static_zero(self.tds, &ty).ok(),
        }
    }

    /// A path into a value the body holds directly rather than in storage.
    ///
    /// A structure parameter passed by value is an F\* record, and a fixed
    /// array inside one is a sequence, so `s.b[i]` is two projections: no
    /// address, no ownership, and no focus to open or close. C agrees that
    /// this reads nothing -- the copy is the parameter -- and the obligation
    /// a subscript carries is the sequence's own pinned length rather than
    /// anything the contract has to say.
    fn value_read(&mut self, e: &Expr) -> Option<String> {
        match &strip_vattr(e).val {
            // Only a name with no storage behind it. A local, an allocated
            // block, an array parameter and an alias all have somewhere the
            // value lives, and reading through that is the access this is
            // not.
            ExprT::Var(v) => {
                let v = v.val.to_string();
                if !self.params.contains(&v) {
                    return None;
                }
                if self.slots.iter().any(|s| s.name == v)
                    || self.blocks.iter().any(|b| b.var == v)
                    || self.arrays.contains_key(&v)
                    || self.aliases.contains_key(&v)
                    || self.is_array_alias(&v)
                {
                    return None;
                }
                Some(format!("var_{}", v))
            }
            ExprT::Member(base, f) => {
                let (_, bty) = self.struct_of(base).ok()?;
                self.field_ty(base, f).ok()?;
                let b = self.value_read(base)?;
                Some(field_value(self.tds, &bty, &b, &f.val.to_string()))
            }
            ExprT::Index(base, idx) => {
                let bty = self.ty_of(base).ok()?;
                if !matches!(peel(self.tds, &bty).val, TypeT::FixedArray(..)) {
                    return None;
                }
                let b = self.value_read(base)?;
                let i = self.index(idx).ok()?;
                Some(format!("(Seq.index {} (SizeT.v {}))", b, i))
            }
            _ => None,
        }
    }

    /// The published length of an array global, if it has one.
    fn global_array_len(&self, v: &Ident) -> Option<u64> {
        let gv = self.env.lookup_global_var(v)?;
        let init = gv.init.as_ref()?;
        const_array(self.tds, &gv.ty, init).map(|(_, n, _)| n)
    }

    fn global_value(&self, v: &Ident) -> bool {
        let Some(gv) = self.env.lookup_global_var(v) else {
            return false;
        };
        // An `extern const` has a value this file cannot write down, but it
        // still has *a* value, published abstractly by the global's own
        // module. Reading it needs no ownership for the same reason reading a
        // known constant does not: nothing in the program can write it, so
        // there is no moment at which the read happens.
        global_has_value(self.tds, gv)
    }

    /// The place an aliased pointer stands for, when `e` dereferences one.
    /// An lvalue with every alias resolved to the place it stands for, so
    /// that two spellings of the same object compare equal.
    fn unalias_place(&self, e: &Expr) -> Rc<Expr> {
        if let Some(p) = self.unalias(e) {
            return self.unalias_place(&p);
        }
        match &strip_vattr(e).val {
            ExprT::Member(b, f) => Rc::new(Ast {
                val: ExprT::Member(self.unalias_place(b), f.clone()),
                loc: e.loc.clone(),
            }),
            ExprT::Deref(b) => Rc::new(Ast {
                val: ExprT::Deref(self.unalias_place(b)),
                loc: e.loc.clone(),
            }),
            _ => Rc::new(e.clone()),
        }
    }

    fn unalias(&self, e: &Expr) -> Option<Rc<Expr>> {
        let ExprT::Deref(inner) = &strip_vattr(e).val else {
            return None;
        };
        let v = lvalue_name(inner)?;
        self.aliases.get(&v).cloned()
    }

    /// Whether a pointer expression is a fixed function of the function's
    /// parameters: the same address every time it is written, computed by
    /// arithmetic on a name the body never rebinds and never read out of
    /// memory.
    ///
    /// Dereferencing one is allowed for the same reason dereferencing a
    /// parameter is. A parameter's pointee is the contract's business -- the
    /// emitter does not check that the ownership is there, it emits the access
    /// and lets slprop matching find it -- and an expression like
    /// `_container_of(node, struct outer, node)` is as much a parameter's
    /// pointee as `node` is, since it denotes one fixed object for the whole
    /// call. A pointer *loaded* out of memory is not: what it addresses
    /// depends on what was stored, which the contract would have to grant
    /// separately.
    /// What a struct's `_own` predicate covers, by C struct name.
    fn own_items_of(&self, sn: &str) -> Vec<OwnItem> {
        self.tds
            .structs
            .get(sn)
            .map(|si| own_items(self.tds, si, sn))
            .unwrap_or_default()
    }

    /// Which `_own` item, if any, holds the object `e` points at.
    ///
    /// The items are named after the path that reaches them -- `z` for what
    /// `s->z` points at, `z_1` for what *that* points at -- so this is a walk
    /// of the same shape over the expression. A parameter the contract does
    /// not really own is not a starting point, because the ownership would
    /// then be one the signature never stated.
    fn own_item(&self, e: &Expr) -> Option<(String, String, String)> {
        match &strip_vattr(e).val {
            // `s->f`, which reaches the IR as `(*s).f`, or `a.f` on a struct
            // passed by value. A parameter is the only root: what a struct
            // reached any other way owns is not something this signature
            // states. The two roots differ only in how the struct's value is
            // spelled -- a ghost binder, or the parameter itself.
            ExprT::Member(base, f) => {
                let p;
                let term;
                match &strip_vattr(base).val {
                    ExprT::Deref(root) => {
                        let ExprT::Var(v) = &strip_vattr(root).val else {
                            return None;
                        };
                        p = v.val.to_string();
                        if !self.granted.contains(&p) {
                            return None;
                        }
                        term = format!("(reveal val_{})", p);
                    }
                    ExprT::Var(v) => {
                        p = v.val.to_string();
                        term = format!("var_{}", p);
                    }
                    _ => return None,
                }
                if !self.params.contains(&p) {
                    return None;
                }
                let ty = self.ty_of(base).ok()?;
                let TypeT::TypeRef(TypeRefKind::Struct(n)) = &peel(self.tds, &ty).val else {
                    return None;
                };
                let sn = n.val.to_string();
                let name = f.val.to_string();
                self.own_items_of(&sn).iter().find(|i| i.name == name)?;
                Some((term, sn, name))
            }
            ExprT::Deref(inner) => {
                let (term, sn, item) = self.own_item(inner)?;
                let name = format!("{}_1", item);
                self.own_items_of(&sn).iter().find(|i| i.name == name)?;
                Some((term, sn, name))
            }
            _ => None,
        }
    }

    /// Fold back every deep ownership this statement unfolded, innermost
    /// first: a later item's address can be an earlier one's value.
    fn close_own(&mut self) {
        for (sn, v) in std::mem::take(&mut self.own_open).into_iter().rev() {
            self.lines.push(format!("{}_own_gather {};", sn, v));
        }
    }

    /// Unfold a struct's deep ownership for the rest of this statement.
    fn open_own(&mut self, v: &str, sn: &str) {
        let sn = format!("struct_{}", sn);
        let v = v.to_string();
        if self.own_open.iter().any(|(s, x)| *s == sn && *x == v) {
            return;
        }
        self.lines.push(format!("{}_own_scatter {};", sn, v));
        self.own_open.push((sn, v));
    }

    fn stable_ptr(&self, e: &Expr) -> bool {
        match &strip_vattr(e).val {
            ExprT::Var(v) => {
                // An alias is a name for a place, and the alias map has
                // already established that the place is the same one for the
                // whole call.
                self.aliases.contains_key(&*v.val.to_string())
                    || (self.params.contains(&*v.val.to_string())
                        && !self.slots.iter().any(|s| s.name == *v.val))
            }
            ExprT::ContainerOf(inner, _, _) | ExprT::Cast(inner, _) => self.stable_ptr(inner),
            _ => false,
        }
    }

    /// Give a named object storage of its own, and copy its value in.
    ///
    /// A C parameter is an ordinary mutable object, but Palow passes it by
    /// value, so it only acquires storage if the body asks for it -- which it
    /// does by taking its address, directly or through an alias.
    fn give_storage(&mut self, name: &str, ty: &Type) -> Result<String, String> {
        if let Some(s) = self.slots.iter().rev().find(|s| s.name == *name) {
            return Ok(s.addr.clone());
        }
        if !has_repr(self.tds, ty) {
            return Err(format!("`{}` is {}", name, describe(self.tds.resolve(ty))));
        }
        let pn = palow_name(self.tds, ty)
            .ok_or_else(|| format!("`{}` has an unsupported type", name))?;
        let fstar_ty =
            fstar_type(self.tds, ty).ok_or_else(|| format!("`{}` has no F* type", name))?;
        self.lines
            .push(format!("let loc_{} = {}_stack_alloc ();", name, pn));
        self.lines
            .push(format!("{}_write_uninit loc_{} var_{};", pn, name, name));
        self.slots.push(Slot {
            name: name.to_string(),
            addr: format!("loc_{}", name),
            palow_ty: pn,
            fstar_ty,
            init: true,
            array: None,
            global: false,
            union_arm: None,
            filling: None,
            holds_fn: BTreeMap::new(),
            scattered: BTreeSet::new(),
        });
        Ok(format!("loc_{}", name))
    }

    /// The address of an lvalue, as an F* expression of type `ptr`.
    fn addr(&mut self, e: &Expr) -> Result<String, String> {
        if let Some(p) = self.unalias(e) {
            return self.addr(&p);
        }
        // The pointer itself, rather than what it points at. Its address is
        // the place's, but handing it out means handing out ownership of the
        // place, which is a focus that has to stay open past this statement.
        if let Some(v) = lvalue_name(e) {
            if self.aliases.contains_key(&v) {
                return Err(format!("`{}`, whose place would have to escape", v));
            }
        }
        match &e.val {
            ExprT::Var(v) => {
                if let Some(s) = self.slots.iter().rev().find(|s| s.name == *v.val) {
                    return Ok(s.addr.clone());
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
                    // was passed in. `give_storage` runs at entry precisely so
                    // that this is not reached for a parameter whose address
                    // the body takes anywhere.
                    return Err(format!("`{}` is addressed inside an `if`", v.val));
                }
                let ty = self.ty_of(e)?;
                self.give_storage(&v.val.to_string(), &ty)
            }
            // The address of `*e` is the value of `e`, but only ownership we
            // can name is ownership we have. A parameter or a local carries its
            // pointee in the contract; a pointer that was itself loaded out of
            // memory -- `*s->next`, `**p` -- does not, and the caller would
            // have had to grant it in a `_requires` that is not translated.
            ExprT::Deref(inner) => match &strip_vattr(inner).val {
                // `*(&e)` is `e`. Clang leaves the pair in the AST, and
                // nothing is loaded by it: the address of a named object is
                // that object's address.
                ExprT::Ref(place) => self.addr(place),
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
                ExprT::Var(v)
                    if self.params.contains(&*v.val.to_string())
                        && self.granted.contains(&*v.val.to_string()) =>
                {
                    self.rvalue(inner)
                }
                // A parameter the contract says nothing about points at
                // memory this function does not hold. Saying so is the whole
                // difference between a weaker specification and a wrong one.
                ExprT::Var(v) if self.params.contains(&*v.val.to_string()) => Err(format!(
                    "a dereference of `{}`, whose ownership the contract does not state",
                    v.val
                )),
                // `malloc` may fail, so an allocation the source never tested
                // is genuinely not owned. This is a real difference from the
                // old model, whose allocator could not return null.
                ExprT::Var(v) if self.blocks.iter().any(|b| b.var == *v.val && !b.freed) => {
                    Err(format!(
                        "a dereference of `{}`, whose allocation was not checked for null",
                        v.val
                    ))
                }
                // A local holding a pointer loaded out of a struct the contract
                // owns deeply. The ownership behind it is in that struct's
                // `_own`, so the access opens it exactly as a direct
                // `*(s->f)` would; whether the local still holds that field's
                // value is left to slprop matching.
                ExprT::Var(v)
                    if self
                        .ptr_src
                        .get(&*v.val.to_string())
                        .is_some_and(|src| self.own_item(src).is_some()) =>
                {
                    let src = self.ptr_src[&*v.val.to_string()].clone();
                    let (p, sn, _) = self.own_item(&src).unwrap();
                    self.open_own(&p, &sn);
                    self.rvalue(inner)
                }
                ExprT::Var(v) if self.spliced_own => self.rvalue(inner),
                ExprT::Var(v) => Err(format!(
                    "a dereference of local `{}`, whose target the contract does not grant",
                    v.val
                )),
                _ if self.stable_ptr(inner) => self.rvalue(inner),
                // A pointer loaded out of a struct the contract deeply owns.
                // `_own` says what it reaches, so unfolding it for the length
                // of this statement is all the access needs; the matching
                // gather is owed at the end of the statement, like any other
                // borrow.
                _ if self.own_item(inner).is_some() => {
                    let (p, sn, _) = self.own_item(inner).unwrap();
                    self.open_own(&p, &sn);
                    self.rvalue(inner)
                }
                // A contract that spliced its own ownership in can have
                // granted anything, in words the emitter does not read. It
                // cannot say what is unowned, so it says nothing and lets
                // slprop matching decide -- which is where the honesty is: if
                // the splice did not grant this, F* rejects the access.
                _ if self.spliced_own => self.rvalue(inner),
                other => Err(format!(
                    "a dereference of {}, whose target the contract does not grant",
                    expr_kind_of(other)
                )),
            },
            // `&s.f` is the structure's address plus the field's offset.
            // Taking an address needs no ownership -- nothing is read by it --
            // so this does not have to open the field the way an access does,
            // and there is no focus left hanging past the statement.
            ExprT::Member(base, f) => {
                let (sn, _) = self.struct_of(base)?;
                self.field_ty(base, f)?;
                let a = self.addr(base)?;
                Ok(format!("({} +! {}_offsetof_{})", a, sn, f.val))
            }
            // `&a[i]` is the array's address plus `i` elements -- but unlike
            // `&s.f`, handing it out is handing out the element, because the
            // only thing that can be done with it is an access. So the element
            // is focused out for the length of the statement and put back
            // afterwards, exactly as a subscript does; the difference is that
            // the access happens in the callee rather than here.
            ExprT::Index(base, idx) => {
                let f = self.focus_elem(base, Some(idx), false)?;
                self.lines.extend(f.open_read.iter().cloned());
                self.pending_close.extend(f.close_write);
                Ok(f.at)
            }
            ExprT::VAttr(_, inner) => self.addr(inner),
            other => Err(format!(
                "{}, which is not an lvalue Palow can address",
                expr_kind_of(other)
            )),
        }
    }

    /// The place an `_out` argument names, looking through an alias and
    /// through the `&` C writes in front of it.
    fn out_place(&self, a: &Expr) -> Option<Rc<Expr>> {
        if let ExprT::Ref(inner) = &strip_vattr(a).val {
            return Some(inner.clone());
        }
        let v = lvalue_name(strip_vattr(a))?;
        self.aliases.get(&v).cloned()
    }

    /// The address an lvalue denotes, computed by arithmetic alone.
    ///
    /// `&e` reads nothing, so it needs no ownership. In Palow an address is
    /// inert until a points-to for it is produced, and an access through this
    /// one will ask for that separately -- so `&p->f` is a subtraction-free
    /// `p +! offsetof_f` even where `*p` is memory this function does not
    /// hold. `addr` is the version for an access, which must know it does.
    fn addr_only(&mut self, e: &Expr) -> Result<String, String> {
        if let Some(p) = self.unalias(e) {
            return self.addr_only(&p);
        }
        if let Some(v) = lvalue_name(e)
            && self.aliases.contains_key(&v)
        {
            return Err(format!("`{}`, whose place would have to escape", v));
        }
        match &strip_vattr(e).val {
            ExprT::Member(base, f) => {
                let (sn, _) = self.struct_of(base)?;
                self.field_ty(base, f)?;
                let a = self.addr_only(base)?;
                Ok(format!("({} +! {}_offsetof_{})", a, sn, f.val))
            }
            ExprT::Deref(inner) => match &strip_vattr(inner).val {
                ExprT::Ref(place) => self.addr_only(place),
                // A checked block is named by the allocation rather than by
                // the local that holds it, so that every mention of it is the
                // same term the frame is stated in.
                ExprT::Var(v)
                    if self
                        .blocks
                        .iter()
                        .any(|b| b.var == *v.val && b.checked && !b.freed) =>
                {
                    Ok(self
                        .blocks
                        .iter()
                        .find(|b| b.var == *v.val && b.checked && !b.freed)
                        .unwrap()
                        .tmp
                        .clone())
                }
                _ => self.rvalue(inner),
            },
            _ => self.addr(e),
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
            // A `ptrdiff_t` is an `int64_t` on this target, and a negative one
            // wraps to the `size_t` whose *addition* is the subtraction C
            // means: `( +! )` is modular, so the address that comes out is the
            // right one either way. Where the index is a subscript rather than
            // an offset it is the array's own bound that rules a negative one
            // out, which is where that obligation belongs.
            TypeT::PtrdiffT => Ok(format!(
                "(sizet_of_uint64 (FStar.Int.Cast.int64_to_uint64 {}))",
                v
            )),
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
    fn place(&mut self, e: &Expr, writing: bool) -> Result<Focus, String> {
        if let Some(p) = self.unalias(e) {
            return self.place(&p, writing);
        }
        match &strip_vattr(e).val {
            ExprT::Member(base, f) if self.union_of(base).is_some() => {
                self.union_member(base, f, writing)
            }
            ExprT::Member(base, f) => {
                let ff = self.open_field(base, f, writing)?;
                // A bit-field's access is an access to its unit: the Palow
                // type is the unit's, and the bits are picked out of the
                // value afterwards rather than addressed.
                let pn = match &ff.bits {
                    Some(pos) => format!("uint{}_t", pos.unit_bits),
                    None => self.field_pn(base, f)?,
                };
                if let Some(focus) = self.scattered_field(&ff, f, &pn, writing) {
                    if ff.bits.is_some() {
                        return Err(format!(
                            "a bit-field of `{}`, whose storage is scattered here",
                            f.val
                        ));
                    }
                    return Ok(focus);
                }
                self.no_value_yet(&ff.a)?;
                self.lines
                    .push(format!("{}_focus_{} {};", ff.sn, ff.field, ff.a));
                let mut close_read = vec![format!("{}_unfocus_read_{} {};", ff.sn, ff.field, ff.a)];
                close_read.extend(ff.close_read);
                let mut close_write = vec![format!("{}_unfocus_{} {};", ff.sn, ff.field, ff.a)];
                close_write.extend(ff.close_write);
                Ok(Focus {
                    write_fn: format!("{}_write", pn),
                    pn,
                    bits: ff.bits,
                    at: ff.at,
                    open_read: Vec::new(),
                    open_write: Vec::new(),
                    close_read,
                    close_write,
                })
            }
            ExprT::Index(base, idx) => self.focus_elem(base, Some(idx), writing),
            _ => Err(format!("a place that is {}", expr_kind_of(&e.val))),
        }
    }

    /// The struct a field belongs to, if the emitter generated a type for it.
    fn struct_of(&self, base: &Expr) -> Result<(String, Rc<Type>), String> {
        let bty = self.ty_of(base)?;
        // `peel`, because a `_refine` written on the typedef that names the
        // struct is still that struct as far as its fields go.
        let TypeT::TypeRef(TypeRefKind::Struct(sname)) = &peel(self.tds, &bty).val else {
            return Err(format!("a field of {}", describe(self.tds.resolve(&bty))));
        };
        if !self.tds.structs.contains_key(&*sname.val) {
            return Err(format!("a field of {}", describe(self.tds.resolve(&bty))));
        }
        Ok((format!("struct_{}", sname.val), bty.clone()))
    }

    /// The union a member belongs to, if the emitter generated a type for it.
    fn union_of(&self, base: &Expr) -> Option<String> {
        let bty = self.ty_of(base).ok()?;
        let TypeT::TypeRef(TypeRefKind::Union(uname)) = &peel(self.tds, &bty).val else {
            return None;
        };
        self.tds
            .unions
            .get(&*uname.val.to_string())
            .map(|_| format!("union_{}", uname.val))
    }

    /// A member access on a union. Unlike a struct field this is not a focus
    /// into a disjoint part of the object: every member starts at the same
    /// address and covers the same bytes, so reading one means claiming the
    /// object *is* that member, and writing one means making it so.
    ///
    /// The two directions are therefore not symmetric. A write works from any
    /// starting value -- `union_X_switch_m` gives up whatever was there and
    /// hands back storage -- while a read needs the live member to be the one
    /// being read, which is a fact about the program and not about the type.
    /// C says the same thing, and says that getting it wrong is not reading
    /// what you wrote; the emitter allows the read exactly where it put the
    /// value there itself.
    fn union_member(&mut self, base: &Expr, f: &Ident, writing: bool) -> Result<Focus, String> {
        let un = self
            .union_of(base)
            .ok_or_else(|| "a member of a union with no Palow type".to_string())?;
        let fty = self.field_ty(base, f)?;
        // An array arm has no single Palow name -- its ownership is the array
        // combinator applied to its element's -- so the whole shape is what
        // the focus has to be spelled with.
        let shape = match field_shape(self.tds, &fty) {
            Some(FieldShape::One { .. }) if palow_name(self.tds, &fty).is_none() => None,
            other => other,
        };
        let Some(shape) = shape else {
            return Err(format!(
                "a union member of type {}",
                describe(self.tds.resolve(&fty))
            ));
        };
        let pn = match &shape {
            FieldShape::One { pn } | FieldShape::Array { pn, .. } | FieldShape::Flex { pn, .. } => {
                pn.clone()
            }
        };
        let (a, base_close_read, base_close_write) = self.base_addr(base, writing)?;
        if !writing && self.active.get(&a).map(String::as_str) != Some(&*f.val.to_string()) {
            // The other way to know is the contract. There the union's value
            // is whatever the caller passed, so the tag is a fact rather than
            // a shape: the ownership in hand is stated at an opaque value,
            // and `focus` wants it stated at the constructor. Re-stating it
            // that way is the whole of the step, and it is sound exactly
            // because the `_requires` said so -- which is why this is not
            // reachable without one.
            let uname = un.strip_prefix("union_").unwrap_or(&un).to_string();
            let ctor = format!("Union_{}_{}", uname, f.val);
            // A pointer bound to the address of a place stands for that
            // place, and the contract names the place: `payload->uds` after
            // `payload = &ctx.payload` is `ctx.payload.uds`.
            let named = self.unalias_place(base);
            // A contract that spliced its own ownership in can have said
            // which member is live too, in words the emitter does not read --
            // `tag_relation` tying the tag to the constructor is exactly
            // that. So the re-statement is emitted and the obligation left to
            // F*, which is where the honesty is: if nothing in the contract
            // implies the tag, the `rewrite` fails.
            if !self.spliced_own
                && !self
                    .live_arms
                    .iter()
                    .any(|(obj, m)| *m == *f.val && same_lvalue(obj, &named))
            {
                return Err(format!(
                    "a read of union member `{}`, which is not known to be the live one here",
                    f.val
                ));
            }
            let vp = self.fresh("perm");
            let vu = self.fresh("union");
            self.lines.push(format!(
                "with {} {}. assert ({}_pts_to {} {} {});",
                vp, vu, un, a, vp, vu
            ));
            self.lines.push(format!(
                "rewrite ({}_pts_to {} {} {}) as ({}_pts_to {} {} ({} ({}?.v {})));",
                un, a, vp, vu, un, a, vp, ctor, ctor, vu
            ));
            self.active.insert(a.clone(), f.val.to_string());
        }
        // Storage that has never been written needs the step that starts from
        // storage rather than from a value -- and once a member has been made
        // active the union holds something, which is what the slot's release
        // has to know.
        let mut uninit_suffix = "";
        if writing {
            self.active.insert(a.clone(), f.val.to_string());
            if let Some(i) = self.slots.iter().rposition(|s| s.addr == a && !s.init) {
                uninit_suffix = "_uninit";
                self.slots[i].init = true;
            }
        }
        let focus = vec![format!("{}_focus_{} {};", un, f.val, a)];
        let close = |mut base: Vec<String>| {
            let mut v = vec![format!("{}_unfocus_{} {};", un, f.val, a)];
            v.append(&mut base);
            v
        };
        Ok(Focus {
            bits: None,
            pn: pn.clone(),
            write_fn: shape.write_fn(),
            at: a.clone(),
            open_read: focus,
            open_write: vec![format!("{}_switch{}_{} {};", un, uninit_suffix, f.val, a)],
            // Whatever had to be opened to name the union is closed after the
            // union itself is, innermost first. Dropping these was invisible
            // until a union nested in a struct reached here.
            close_read: close(base_close_read),
            close_write: close(base_close_write),
        })
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
    /// Open a field of an object that is being built one field at a time,
    /// if that is what this access is.
    ///
    /// `struct S s; s.f = x; s.g = y;` has no point at which `s` is a struct:
    /// the first assignment writes a field of storage, and only the last one
    /// completes an object. A focus cannot describe that, because a focus
    /// opens a value and puts the same value back. So the object is scattered
    /// into its fields' storage on the first write and gathered back into a
    /// value on the last, and in between each field is written -- or read --
    /// through its own address, with nothing open around it.
    fn scattered_field(
        &mut self,
        ff: &FieldFocus,
        f: &Ident,
        pn: &str,
        writing: bool,
    ) -> Option<Focus> {
        let sname = ff.sn.strip_prefix("struct_")?;
        let si = self.tds.structs.get(sname)?;
        // The scatter and gather operations only exist when the struct got an
        // uninitialised view, which needs every field to have one.
        if !si.fields.iter().all(|x| match &x.shape {
            FieldShape::One { .. } => has_repr(self.tds, &x.ty),
            FieldShape::Array { .. } => true,
            FieldShape::Flex { .. } => false,
        }) {
            return None;
        }
        let names: Vec<String> = si.fields.iter().map(|x| x.name.clone()).collect();
        if !names.iter().any(|n| n == &*f.val) {
            return None;
        }
        // A local's storage and an allocated block's differ in where they came
        // from and in nothing else: both are uninitialised until every field
        // has been written, and both are filled the same way.
        let target = match self
            .slots
            .iter()
            .rposition(|s| s.addr == ff.a && !s.init && s.array.is_none())
        {
            Some(i) => Scattering::Slot(i),
            None => Scattering::Block(self.blocks.iter().rposition(|b| {
                b.tmp == ff.a && b.checked && !b.freed && !b.init && b.array.is_none()
            })?),
        };
        if !writing {
            if !self.scattered_set(target).contains(&*f.val) {
                return None;
            }
            return Some(Focus {
                bits: None,
                write_fn: format!("{}_write", pn),
                pn: pn.to_string(),
                at: ff.at.clone(),
                open_read: Vec::new(),
                open_write: Vec::new(),
                // Whatever had to be opened to reach the storage is still
                // open: scattering happens *inside* that, not instead of it.
                close_read: ff.close_read.clone(),
                close_write: ff.close_write.clone(),
            });
        }
        if self.scattered_set(target).is_empty() {
            self.lines
                .push(format!("{}_scatter_uninit {};", ff.sn, ff.a));
        }
        self.scattered_set_mut(target).insert(f.val.to_string());
        let mut close_write = Vec::new();
        if names.iter().all(|n| self.scattered_set(target).contains(n)) {
            close_write.push(format!("{}_gather {};", ff.sn, ff.a));
            // An arm that is complete is a value of the arm's type, and what
            // holds it is the union: putting it back is what turns the last
            // field write into a whole-member write after the fact.
            if let Scattering::Slot(i) = target
                && let Some((un, arm)) = self.slots[i].union_arm.clone()
            {
                close_write.push(format!("{}_unfocus_{} {};", un, arm, ff.a));
            }
            self.scattered_set_mut(target).clear();
            match target {
                Scattering::Slot(i) => self.slots[i].init = true,
                Scattering::Block(i) => self.blocks[i].init = true,
            }
        }
        // Whatever had to be opened to reach the storage is still open:
        // scattering happens *inside* that, not instead of it.
        close_write.extend(ff.close_write.iter().cloned());
        Some(Focus {
            bits: None,
            write_fn: format!("{}_write_uninit", pn),
            pn: pn.to_string(),
            at: ff.at.clone(),
            open_read: Vec::new(),
            open_write: Vec::new(),
            close_read: Vec::new(),
            close_write,
        })
    }

    /// The fields written so far into whichever of the two kinds of storage is
    /// being filled.
    fn scattered_set(&self, t: Scattering) -> &BTreeSet<String> {
        match t {
            Scattering::Slot(i) => &self.slots[i].scattered,
            Scattering::Block(i) => &self.blocks[i].scattered,
        }
    }

    fn scattered_set_mut(&mut self, t: Scattering) -> &mut BTreeSet<String> {
        match t {
            Scattering::Slot(i) => &mut self.slots[i].scattered,
            Scattering::Block(i) => &mut self.blocks[i].scattered,
        }
    }

    /// Everything `focus_field` does except emitting the focus itself.
    fn open_field(&mut self, base: &Expr, f: &Ident, writing: bool) -> Result<FieldFocus, String> {
        let (sn, bty) = self.struct_of(base)?;
        let (field, bits) = match bitfield_at(self.tds, &bty, &f.val.to_string()) {
            Some(b) => (b.unit.clone(), Some(b.pos.clone())),
            None => (f.val.to_string(), None),
        };
        let (a, close_read, close_write) = self.base_addr(base, writing)?;
        let at = format!("({} +! {}_offsetof_{})", a, sn, field);
        Ok(FieldFocus {
            sn,
            field,
            bits,
            a,
            at,
            close_read,
            close_write,
        })
    }

    fn focus_field(&mut self, base: &Expr, f: &Ident, writing: bool) -> Result<FieldFocus, String> {
        let ff = self.open_field(base, f, writing)?;
        self.no_value_yet(&ff.a)?;
        self.lines
            .push(format!("{}_focus_{} {};", ff.sn, ff.field, ff.a));
        Ok(ff)
    }

    /// A field focus splits a points-to, and freshly allocated storage has
    /// none: it holds bytes, not a value. Where the struct has an
    /// uninitialised view the object is scattered into its fields instead --
    /// see `scattered_field` -- but a focus proper has nothing to split.
    fn no_value_yet(&self, at: &str) -> Result<(), String> {
        match self
            .blocks
            .iter()
            .find(|b| b.tmp == *at && b.checked && !b.freed && !b.init)
        {
            Some(b) => Err(format!("a field of `{}`, which holds no value yet", b.var)),
            None => Ok(()),
        }
    }

    /// The address of the object a field belongs to. Usually just `addr`, but
    /// a field of a *nested* struct -- which is what an anonymous member and a
    /// first-field cast both come out as -- has to focus the outer field first,
    /// and that focus stays open until the access through it is done.
    fn base_addr(
        &mut self,
        base: &Expr,
        writing: bool,
    ) -> Result<(String, Vec<String>, Vec<String>), String> {
        if let Some(p) = self.unalias(base) {
            return self.base_addr(&p, writing);
        }
        // A struct-typed union arm that has been activated is storage at the
        // union's own address: every arm starts there, and activation gave up
        // the union's value in exchange for the arm's uninitialised storage.
        // A field of it is therefore reached by address, with nothing open
        // around it -- which is what lets the fields be filled one at a time.
        if let ExprT::Member(b2, f2) = &strip_vattr(base).val
            && let Ok(bty) = self.ty_of(b2)
            && matches!(
                &peel(self.tds, &bty).val,
                TypeT::TypeRef(TypeRefKind::Union(_))
            )
            && let Ok(a) = self.addr(b2)
            && self.active.get(&a).map(String::as_str) == Some(&*f2.val.to_string())
            && self.slots.iter().any(|s| s.addr == a && !s.init)
        {
            return Ok((a, Vec::new(), Vec::new()));
        }
        if let ExprT::Member(b2, f2) = &strip_vattr(base).val {
            let fty = self.field_ty(b2, f2)?;
            // A union-typed field is reached the same way: the aggregate
            // holding it has to be opened before anything inside it can be
            // named, and which of the two it is changes nothing about that.
            if matches!(
                &peel(self.tds, &fty).val,
                TypeT::TypeRef(TypeRefKind::Struct(_) | TypeRefKind::Union(_))
            ) {
                let inner = self.focus_field(b2, f2, writing)?;
                let mut close_read =
                    vec![format!("{}_unfocus_read_{} {};", inner.sn, f2.val, inner.a)];
                close_read.extend(inner.close_read);
                let mut close_write = vec![format!("{}_unfocus_{} {};", inner.sn, f2.val, inner.a)];
                close_write.extend(inner.close_write);
                return Ok((inner.at, close_read, close_write));
            }
        }
        // `p->f` where `p` is an array parameter is `p[0].f`: the ownership
        // is a sequence, so the element has to be focused out of it before
        // the field can be focused out of the element. Without this the field
        // focus would be applied to the array itself.
        if let ExprT::Deref(inner) = &strip_vattr(base).val
            && let ExprT::Var(v) = &strip_vattr(inner).val
            && self.arrays.contains_key(&v.val.to_string())
        {
            let inner = inner.clone();
            let f = self.focus_elem(&inner, None, false)?;
            // The element has to be *opened* as well as focused: a block whose
            // elements may be uninitialised is owned at the `maybe` view, and
            // a field of one cannot be reached until the element has been
            // turned into a value of its type. Dropping these was how a field
            // of a `calloc`ed struct came out as a focus with nothing under it.
            self.lines.extend(if writing {
                f.open_write.clone()
            } else {
                f.open_read.clone()
            });
            return Ok((f.at, f.close_read, f.close_write));
        }
        // The same for `a[i].f`, and for every kind of array there is: a
        // parameter, a local, a global, an allocated block. Which of them the
        // sequence is owned through changes where the ownership came from and
        // nothing about the access.
        if let ExprT::Index(arr, idx) = &strip_vattr(base).val
            && self.is_array_place(arr)
        {
            let mark = self.lines.len();
            let f = self.focus_elem(arr, Some(idx), false)?;
            // An element `$unfold-uninit` already opened stays open: the
            // focus is standing, so taking it again would be taking the
            // ownership twice. There is no way to ask for the address without
            // computing it, so the focus is emitted and then withdrawn.
            if self.open_elems.iter().any(|(a, _)| *a == f.at) {
                self.lines.truncate(mark);
                return Ok((f.at, Vec::new(), Vec::new()));
            }
            self.lines.extend(if writing {
                f.open_write.clone()
            } else {
                f.open_read.clone()
            });
            return Ok((f.at, f.close_read, f.close_write));
        }
        Ok((self.addr(base)?, Vec::new(), Vec::new()))
    }

    /// Whether this expression names an array whose elements the body can
    /// focus: a parameter, a local, a mutable global, or an allocated block.
    /// The mirror of `array_place`'s cases, asked before committing to one.
    fn is_array_place(&self, e: &Expr) -> bool {
        let ExprT::Var(v) = &strip_vattr(e).val else {
            return false;
        };
        let v = self.array_alias(&v.val.to_string());
        self.blocks
            .iter()
            .any(|b| b.var == v && b.checked && !b.freed && b.array.is_some())
            || self.slots.iter().any(|s| s.name == v && s.array.is_some())
            || self.arrays.contains_key(&v)
    }

    /// The array a local is another name for, or the name itself.
    fn array_alias(&self, v: &str) -> String {
        match self.array_aliases.get(v) {
            Some(a) if self.names_array(a) => a.clone(),
            _ => v.to_string(),
        }
    }

    /// Whether this local is another name for an array rather than storage.
    fn is_array_alias(&self, v: &str) -> bool {
        self.array_aliases
            .get(v)
            .is_some_and(|a| self.names_array(a))
    }

    fn names_array(&self, v: &str) -> bool {
        self.slots.iter().any(|s| s.name == *v && s.array.is_some()) || self.arrays.contains_key(v)
    }

    /// Whether the number of elements at this array is settled here rather
    /// than being whatever the caller passed.
    fn array_len_known(&self, e: &Expr) -> bool {
        let ExprT::Var(v) = &strip_vattr(e).val else {
            return false;
        };
        if self
            .blocks
            .iter()
            .any(|b| b.var == *v.val && b.checked && !b.freed && b.array.is_some())
        {
            return true;
        }
        if self
            .slots
            .iter()
            .any(|s| s.name == *v.val && s.array.is_some())
        {
            return true;
        }
        self.arrays
            .get(&v.val.to_string())
            .is_some_and(|a| a.known_len)
    }

    /// The array an element access indexes: its base address, element type and
    /// size, and the lines that give it back. Either a parameter, which owns
    /// its sequence outright, or a fixed-size array field, which has to be
    /// focused out of its struct first.
    fn array_place(&mut self, e: &Expr) -> Result<ArrayPlace, String> {
        match &strip_vattr(e).val {
            ExprT::Var(v) => {
                // A local that is another name for an array is that array:
                // the decay copied no elements, and the ownership the
                // contract granted is the one the subscript needs.
                let v = self.array_alias(&v.val.to_string());
                // An allocated block is looked at before the pointer local is,
                // because the local holds the same address and going through it
                // would mean a load whose result the frame would then have to
                // be restated in terms of.
                if let Some(b) = self
                    .blocks
                    .iter()
                    .find(|b| b.var == v && b.checked && !b.freed && b.array.is_some())
                {
                    let a = b.array.clone().unwrap();
                    return Ok(ArrayPlace {
                        addr: b.tmp.clone(),
                        pn: b.pn.clone(),
                        esize: a.esize,
                        base: 0,
                        close_read: Vec::new(),
                        close_write: Vec::new(),
                        maybe: true,
                    });
                }
                // A local array's elements are `option`s; a parameter's are
                // not, because the caller has already initialised them.
                if let Some(s) = self.slots.iter().rev().find(|s| s.name == v) {
                    let Some(esize) = s.array.clone() else {
                        return Err(format!("a subscript of local `{}`", v));
                    };
                    return Ok(ArrayPlace {
                        addr: s.addr.clone(),
                        pn: s.palow_ty.clone(),
                        esize: esize.0,
                        base: 0,
                        close_read: Vec::new(),
                        close_write: Vec::new(),
                        maybe: esize.1,
                    });
                }
                let Some(ap) = self.arrays.get(&v) else {
                    return Err(format!(
                        "a subscript of `{}`, which is not an array parameter",
                        v
                    ));
                };
                // An array parameter's length is whatever the caller passed, so
                // `i < Seq.length xs` can only come from the function's own
                // `_requires`. An array *field*'s length is part of its type,
                // so it needs no such help -- hence the gate is here and not in
                // `focus_elem`.
                if !ap.known_len && !self.requires_ok {
                    return Err(
                        "a subscript, whose bounds obligation needs a `_requires` that is not \
                         translated"
                            .to_string(),
                    );
                }
                Ok(ArrayPlace {
                    addr: ap.addr.clone(),
                    pn: ap.pn.clone(),
                    esize: ap.esize.clone(),
                    base: 0,
                    close_read: Vec::new(),
                    close_write: Vec::new(),
                    maybe: ap.maybe,
                })
            }
            // An array arm of a union. The arm has to be the live one
            // already: focusing it hands back the whole sequence, so writing
            // an element and handing it back is an ordinary update, while
            // *activating* a dead arm yields storage that stays storage until
            // every element has been written -- which is a fact that would
            // have to be carried across statements, and is not.
            ExprT::Member(b2, f) if self.union_of(b2).is_some() => {
                // An arm a `$activate` handed over is not the union's value
                // any more: it is storage held directly at the union's own
                // address, so there is nothing to focus out of and nothing to
                // put back until it is full.
                if let Ok(a) = self.addr_only(b2)
                    && let Some(sl) = self.slots.iter().rev().find(|s| {
                        s.addr == a
                            && s.filling.is_some()
                            && s.union_arm.as_ref().map(|(_, m)| m.as_str())
                                == Some(&*f.val.to_string())
                    })
                {
                    return Ok(ArrayPlace {
                        addr: a.clone(),
                        pn: sl.palow_ty.clone(),
                        esize: sl.array.clone().unwrap().0,
                        base: 0,
                        close_read: Vec::new(),
                        close_write: Vec::new(),
                        maybe: true,
                    });
                }
                let fty = self.field_ty(b2, f)?;
                let Some(FieldShape::Array { pn, esize, .. }) = field_shape(self.tds, &fty) else {
                    return Err(format!(
                        "a subscript of a union member of type {}",
                        describe(self.tds.resolve(&fty))
                    ));
                };
                let uf = self.union_member(b2, f, false)?;
                self.lines.extend(uf.open_read.iter().cloned());
                Ok(ArrayPlace {
                    addr: uf.at,
                    pn,
                    esize: format!("{}sz", esize),
                    close_read: uf.close_read,
                    close_write: uf.close_write,
                    maybe: false,
                    base: 0,
                })
            }
            ExprT::Member(base, f) => {
                let fty = self.field_ty(base, f)?;
                // An `_array` field holds a pointer, not the elements, so its
                // storage is not inside the struct at all: it is what the
                // struct's deep ownership claims. The address still has to be
                // read out of the field, which is an ordinary rvalue.
                if let Some((term, sn, item)) = self.own_item(e)
                    && let Some(i) = self
                        .own_items_of(&sn)
                        .into_iter()
                        .find(|i| i.name == item && i.esize.is_some())
                {
                    self.open_own(&term, &sn);
                    let addr = self.rvalue(e)?;
                    return Ok(ArrayPlace {
                        addr,
                        pn: i.pn,
                        esize: format!("{}sz", i.esize.unwrap()),
                        base: 0,
                        close_read: Vec::new(),
                        close_write: Vec::new(),
                        maybe: false,
                    });
                }
                let (pn, esize) = match field_shape(self.tds, &fty) {
                    Some(FieldShape::Array { pn, esize, .. } | FieldShape::Flex { pn, esize }) => {
                        (pn, esize)
                    }
                    _ => {
                        return Err(format!(
                            "a subscript of a field of type {}",
                            describe(self.tds.resolve(&fty))
                        ));
                    }
                };
                let ff = self.focus_field(base, f, false)?;
                // A read goes back with the field's read-only unfocus, which
                // hands the struct back at the very value it had. The general
                // one rebuilds the record field by field, and a rebuilt record
                // is only the original up to eta -- which is enough for F* but
                // not for the syntactic match that finds the struct's deep
                // ownership in the context.
                let mut close_read = vec![format!("{}_unfocus_read_{} {};", ff.sn, f.val, ff.a)];
                let mut close_write = vec![format!("{}_unfocus_{} {};", ff.sn, f.val, ff.a)];
                close_read.extend(ff.close_read);
                close_write.extend(ff.close_write);
                Ok(ArrayPlace {
                    addr: ff.at,
                    pn,
                    esize: format!("{}sz", esize),
                    base: 0,
                    close_read,
                    close_write,
                    maybe: false,
                })
            }
            // `m->arr[2][3]`: the outer subscript of a multidimensional array
            // picks a row, and a row is not an object of its own. C lays the
            // rows out end to end, so the place is still the whole flat field
            // and the row contributes nothing but an offset to the index.
            ExprT::Index(inner, j) => {
                let ity = self.ty_of(e)?;
                let Some((_, rowlen)) = flat_array(self.tds, &ity) else {
                    return Err("a subscript of an array element".to_string());
                };
                let Some(k) = const_index(&strip_vattr(j).val) else {
                    return Err(
                        "a row of a multidimensional array chosen at a variable index".to_string(),
                    );
                };
                let mut ap = self.array_place(inner)?;
                ap.base += k * rowlen;
                Ok(ap)
            }
            other => Err(format!("a subscript of {}", expr_kind_of(other))),
        }
    }

    /// Open one element of an array for a single access.
    fn focus_elem(
        &mut self,
        base: &Expr,
        idx: Option<&Expr>,
        writing: bool,
    ) -> Result<Focus, String> {
        // `array_focus` demands `i < Seq.length xs`. A constant index of an
        // array whose extent is in its type carries that bound with it;
        // anything else is the function's own `_requires` saying so, and
        // emitting the access without one produces a failure about the
        // subscript rather than about the memory model.
        let bounded = match (idx, &strip_vattr(base).val) {
            (None, _) => true,
            (Some(e), ExprT::Var(v)) => {
                let n = self.global_array_len(v).unwrap_or(0);
                const_index(&strip_vattr(e).val).is_some_and(|k| k < n)
            }
            _ => false,
        };
        if !bounded && !self.signed_ok {
            return Err(
                "a subscript, whose bounds obligation needs the untranslated `_requires`"
                    .to_string(),
            );
        }
        let ArrayPlace {
            addr: arr,
            pn,
            esize,
            close_read: cl_read,
            close_write: cl_write,
            maybe,
            base: elem_base,
        } = self.array_place(base)?;
        let i = match idx {
            Some(e) => self.index(e)?,
            None => "0sz".to_string(),
        };
        // A row offset is only usable if it can be folded into the index: the
        // flat index is `row * width + i`, and an addition of two `size_t`s
        // carries a `fits` obligation that nothing here is in a position to
        // discharge. A literal index needs no addition at all.
        let i = if elem_base == 0 {
            i
        } else {
            match i.strip_suffix("sz").and_then(|d| d.parse::<u64>().ok()) {
                Some(k) => format!("{}sz", k + elem_base),
                None => {
                    return Err(
                        "a subscript of a multidimensional array at a variable index".to_string(),
                    );
                }
            }
        };
        let off = format!("({} `SizeT.mul` {})", esize, i);
        let at = format!("({} +! {})", arr, off);
        let repr = if maybe {
            format!("(maybe_repr {}_repr (SizeT.v {}))", pn, esize)
        } else {
            format!("{}_repr", pn)
        };
        self.lines.push(format!(
            "array_offset_fits {} {} {} {};",
            repr, arr, esize, i
        ));
        self.lines.push(format!(
            "array_focus {} {} {} {} {};",
            repr, arr, esize, i, off
        ));
        let common = format!("{} {} {} {}", arr, esize, i, off);
        if !maybe {
            self.lines.push(format!("{}_of_elem {};", pn, at));
            let mut close_read = vec![
                format!("{}_to_elem {};", pn, at),
                format!("array_unfocus_read {} {};", repr, common),
            ];
            let mut close_write = vec![
                format!("{}_to_elem {};", pn, at),
                format!("array_unfocus {} {};", repr, common),
            ];
            close_read.extend(cl_read);
            close_write.extend(cl_write);
            return Ok(Focus {
                bits: None,
                at,
                write_fn: format!("{}_write", pn),
                pn,
                open_read: Vec::new(),
                open_write: Vec::new(),
                close_read,
                close_write,
            });
        }
        // Reading needs the element to hold a value, which is where C's rule
        // about uninitialised objects turns into an obligation. Writing does
        // not: it goes down to the raw bytes and comes back up through the
        // type's own write-only view, exactly as a scalar local does.
        let open_read = vec![
            format!("elem_maybe_get {}_repr {} {};", pn, esize, at),
            format!("{}_of_elem {};", pn, at),
        ];
        let open_write = vec![
            format!("elem_maybe_reveal {}_repr {} {};", pn, esize, at),
            format!("{}_claim_uninit {};", pn, at),
        ];
        // Both directions close through `array_unfocus`, even the read: what
        // comes back is `Some` of what was there, which is the same element
        // only up to a proof, and `array_unfocus_read` matches syntactically.
        let mut both = vec![
            format!("{}_to_elem {};", pn, at),
            format!("elem_maybe_put {}_repr {} {};", pn, esize, at),
            format!("array_unfocus {} {};", repr, common),
        ];
        let mut close_write = both.clone();
        let mut close_read = both;
        // A union arm handed over by `$activate` is storage until every one of
        // its elements holds a value. The write that fills the last one is
        // what turns the arm back into a value of the arm's type, and the
        // union is what holds it -- the same step a struct arm's last field
        // write takes, counted by index instead of by name.
        if writing
            && let Some(k) = i.strip_suffix("sz").and_then(|d| d.parse::<u64>().ok())
            && let Some(si) = self
                .slots
                .iter()
                .rposition(|s| s.addr == arr && s.filling.is_some())
        {
            let full = {
                let (n, set) = self.slots[si].filling.as_mut().unwrap();
                set.insert(k);
                let n = *n;
                (0..n).all(|j| set.contains(&j))
            };
            if full {
                let (un, arm) = self.slots[si].union_arm.clone().unwrap();
                close_write.push(format!(
                    "array_claim_all_somes {}_repr {} {};",
                    pn, arr, esize
                ));
                close_write.push(format!("{}_unfocus_{} {};", un, arm, arr));
                self.slots.remove(si);
            }
        }
        close_read.extend(cl_read);
        close_write.extend(cl_write);
        Ok(Focus {
            bits: None,
            at,
            write_fn: format!("{}_write_uninit", pn),
            pn,
            open_read,
            open_write,
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
        if let ExprT::Var(v) = &strip_vattr(e).val {
            if let Some(b) = self.spec_binders.get(v.val.as_ref()) {
                return Ok(b.clone());
            }
        }
        let before = self.lines.len();
        let mut v = match self.rvalue(e) {
            Ok(v) => v,
            // A ghost fragment wants the *value* of an object, and a load is
            // only one way to get one -- the expensive way, which needs the
            // object to have a whole-value read at all. The ownership in hand
            // already determines the value, so where a load is impossible the
            // witness of the points-to is named instead. That is what makes a
            // struct with a union member mentionable in a ghost statement:
            // there is no reading such an object, but there is a value, and
            // the proof is about the value.
            Err(why) => {
                self.lines.truncate(before);
                return self.ghost_value(e).ok_or(why);
            }
        };
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

    /// The ghost value of an object, named rather than read.
    ///
    /// `with x. assert (S_pts_to a p x)` binds the witness the ownership
    /// already has. It costs nothing -- no permission beyond what is held, no
    /// load -- and unlike a read it works for an object whose type has no
    /// whole-value read, which is exactly the case a ghost statement about a
    /// tagged union runs into.
    fn ghost_value(&mut self, e: &Expr) -> Option<String> {
        let ty = self.ty_of(e).ok()?;
        if !matches!(
            peel(self.tds, &ty).val,
            TypeT::TypeRef(TypeRefKind::Struct(_) | TypeRefKind::Union(_))
        ) {
            return None;
        }
        let pn = palow_name(self.tds, &ty)?;
        let (a, close_read, _) = self.base_addr(e, false).ok()?;
        let vp = self.fresh("perm");
        let vv = self.fresh("val");
        self.lines.push(format!(
            "with {} {}. assert ({}_pts_to {} {} {});",
            vp, vv, pn, a, vp, vv
        ));
        self.lines.extend(close_read);
        Some(vv)
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
            // Which member of a union is live. The contract can read the tag
            // straight off a value it has a binder for; a body has no such
            // binder, so it names the union's current value the only way it
            // can -- by asserting the ownership it already holds and binding
            // the witness -- and applies the discriminator to that. Whatever
            // had to be opened to reach the union is closed again right
            // after: the binder is a ghost value and outlives its slprop.
            ExprT::VAttr(VAttr::Active(m), obj) => {
                let un = self
                    .union_of(obj)
                    .ok_or_else(|| "a member of a union with no Palow type".to_string())?;
                let uname = un.strip_prefix("union_").unwrap_or(&un).to_string();
                let (a, close_read, _) = self.base_addr(obj, false)?;
                let vp = self.fresh("perm");
                let vu = self.fresh("union");
                self.lines.push(format!(
                    "with {} {}. assert ({}_pts_to {} {} {});",
                    vp, vu, un, a, vp, vu
                ));
                self.lines.extend(close_read);
                Ok(format!("(Union_{}_{}? {})", uname, m.val, vu))
            }
            ExprT::VAttr(_, inner) => self.prop(inner),
            ExprT::Cast(inner, to) if matches!(self.tds.resolve(to).val, TypeT::SLProp) => {
                self.prop(inner)
            }
            ExprT::Old(_) => Err("an assertion about the state on entry".to_string()),
            ExprT::InlinePulse(code, _) => {
                if !self.tds.splice_inline {
                    return Err(self.tds.no_splice());
                }
                flatten_fragment(&self.inline_pulse(code)?)
            }
            ExprT::UnOp(UnOp::Not, inner) => Ok(format!("(~({}))", self.prop(inner)?)),
            // An assertion translates by *emitting* the loads its operands
            // need, which is exactly what a quantifier body cannot do: a load
            // under a binder would have to run once per witness. So a
            // quantified assertion is translated only when its body turns out
            // to need no memory at all, and the check is made after the fact by
            // seeing whether anything was emitted.
            ExprT::Forall(v, ty, body) | ExprT::Exists(v, ty, body) => {
                let all = matches!(&e.val, ExprT::Forall(..));
                let fty = fstar_type(self.tds, ty).ok_or_else(|| {
                    format!("a quantifier over {}", describe(self.tds.resolve(ty)))
                })?;
                let bound = format!("var_{}", v.val);
                let saved_env = self.env.clone();
                self.env
                    .push_var_decl(v, ty.clone(), crate::env::LocalDeclKind::RValue);
                let shadowed = self.spec_binders.insert(v.val.to_string(), bound.clone());
                let before = self.lines.len();
                let r = self.prop(body);
                let emitted = self.lines.len() != before;
                self.lines.truncate(before);
                self.env = saved_env;
                match shadowed {
                    Some(old) => self.spec_binders.insert(v.val.to_string(), old),
                    None => self.spec_binders.remove(v.val.as_ref()),
                };
                let p = r?;
                if emitted {
                    return Err("a quantified assertion whose body reads memory".to_string());
                }
                Ok(format!(
                    "({} ({}: {}). {})",
                    if all { "forall" } else { "exists" },
                    bound,
                    fty,
                    p
                ))
            }
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
                match self.tds.resolve(&ty).val {
                    TypeT::Bool => Ok(format!("({} == true)", self.inline(e)?)),
                    // C has no separate notion of truth: a condition is a
                    // number, and it holds when that number is not zero. An
                    // assertion is a condition, so `_assert(false)` -- which
                    // is the integer literal 0 once the preprocessor is done
                    // -- means exactly this and nothing more special.
                    TypeT::Int { .. } | TypeT::SizeT | TypeT::SpecInt | TypeT::SpecNat => {
                        Ok(format!("({} <> 0)", self.num(e)?))
                    }
                    _ => Err(format!("{} in an assertion", expr_kind(e))),
                }
            }
        }
    }

    /// A specification expression inside a body, as a mathematical integer.
    fn num(&mut self, e: &Expr) -> Result<String, String> {
        // `p._length` is how the source asks how long an array is. For a block
        // this body allocated the answer is the count it asked for -- the
        // sequence it was claimed at has exactly that length -- so the question
        // is settled here rather than being a fact about a ghost binder that
        // would have to be brought into scope to state.
        if let ExprT::VAttr(VAttr::Length, inner) = &e.val {
            if let ExprT::Var(v) = &strip_vattr(inner).val {
                if let Some(b) = self.blocks.iter().find(|b| b.var == *v.val && !b.freed) {
                    if let Some(a) = &b.array {
                        return Ok(format!("(SizeT.v {})", a.n));
                    }
                }
            }
        }
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
                // A `_let` function is an F* term, so naming it in an
                // assertion is not making a call: nothing runs, and the
                // result is already a mathematical integer.
                ExprT::FnCall(name, _) if self.tds.pure_fns.contains(&*name.val.to_string()) => {
                    return self.inline(e);
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

    /// The function a decay names, if the expression is one.
    fn fn_ref_of(&self, e: &Expr) -> Option<String> {
        match &strip_vattr(e).val {
            ExprT::FnRef(g) => Some(g.val.to_string()),
            ExprT::Ref(inner) | ExprT::Cast(inner, _) => self.fn_ref_of(inner),
            _ => None,
        }
    }

    /// The function an expression must evaluate to, when that is decidable
    /// here.
    ///
    /// A code address is the one pointer value whose *identity* the caller
    /// needs, not just its bytes: `is_valid` says what the code at an address
    /// does, and no points-to carries that. So an indirect call is translated
    /// exactly when the emitter can say which function is being called --
    /// either because a local slot was seen to be set to it, or because the
    /// address was written down in something immutable, where a constant path
    /// reaches it the same way a constant read of any other global does.
    fn target_of(&self, e: &Expr) -> Option<String> {
        if let Some(p) = self.unalias(e) {
            return self.target_of(&p);
        }
        let e = strip_vattr(e);
        if let Some(g) = self.fn_ref_of(e) {
            return Some(g);
        }
        match &e.val {
            ExprT::Deref(inner) => self.target_of(inner),
            _ => {
                // Storage this body owns: what it holds is what was last
                // stored, which is in view here. Anything else -- a global,
                // an initialised constant -- is reached by reading the
                // declaration it was written in.
                if let Some((slot, path)) = self.place_key(e)
                    && let Some(s) = self.slots.iter().rev().find(|s| s.name == slot)
                {
                    return s.holds_fn.get(&path).cloned();
                }
                self.fn_ref_of(self.const_path(e)?.1?.as_ref())
            }
        }
    }

    /// A fragment of hand-written Pulse, spliced in as written.
    ///
    /// The point of an escape hatch is that the text is the author's, so the
    /// only thing to translate is the antiquotations -- and those are exactly
    /// the places where the fragment has to name something only the emitter
    /// knows. `$(e)` is a C value, so it becomes whatever `e` reads as; `$&(e)`
    /// is a C object, so it becomes its address; `$type` and `$field` become
    /// the generated names.
    ///
    /// `$unfold` and friends name helpers the old emitter generated around its
    /// own representation of a struct. Palow's representation is different, so
    /// there is nothing honest to point them at, and they are refused.
    fn inline_pulse(&mut self, code: &InlinePulseCode) -> Result<String, String> {
        let mut out = String::new();
        for tok in &code.tokens {
            match tok {
                InlinePulseToken::Verbatim(ct) => {
                    out.push_str(ct.before);
                    out.push_str(&ct.text.val);
                }
                InlinePulseToken::RValueAntiquot { before, expr } => {
                    // `inline` rather than `rvalue`: a fragment is a single
                    // term, so the loads it needs belong inside it, and a call
                    // is refused because splicing one would run it.
                    let v = match (&strip_vattr(expr).val, &self.ret_binding) {
                        (ExprT::Var(n), Some(r)) if &*n.val == "return" => r.clone(),
                        _ => self.inline(expr)?,
                    };
                    out.push_str(before);
                    out.push_str(&format!("({})", v));
                }
                InlinePulseToken::LValueAntiquot { before, expr } => {
                    let a = self.addr(expr)?;
                    out.push_str(before);
                    out.push_str(&format!("({})", a));
                }
                InlinePulseToken::TypeAntiquot { before, ty } => {
                    let t = fstar_type(self.tds, ty)
                        .ok_or_else(|| format!("`$type` of {}", describe(ty)))?;
                    out.push_str(before);
                    out.push_str(&format!("({})", t));
                }
                InlinePulseToken::FieldAntiquot {
                    before,
                    ty,
                    field_name,
                } => {
                    let n = field_antiquot(self.tds, ty, field_name)?;
                    out.push_str(before);
                    out.push_str(&n);
                }
                InlinePulseToken::AuxFnAntiquot { kind, .. } => {
                    return Err(format!(
                        "`${}`, which names a helper of the old memory model",
                        kind.keyword()
                    ));
                }
                InlinePulseToken::Declare { .. } => {
                    return Err("`$declare` in a statement".to_string());
                }
            }
        }
        Ok(out)
    }

    /// Record which union member a whole-union store makes live.
    ///
    /// C says the member you last wrote is the one you may read, and a brace
    /// initialiser names exactly one. Storing the value is what tags it, so
    /// the emitter can see the tag in the source expression and does not have
    /// to read it back out of a value it just erased.
    fn note_union_store(&mut self, lhs: &Expr, rhs: &Expr) {
        let ExprT::UnionInit(_, m, _) = &strip_vattr(rhs).val else {
            return;
        };
        if let Ok(a) = self.addr(lhs) {
            self.active.insert(a, m.val.to_string());
        }
    }

    /// Which slot an lvalue lives in, and where within it: the empty path for
    /// the slot itself, `op` for its field of that name. Only storage this
    /// body owns outright is reachable this way -- a dereference leads
    /// somewhere else and stops the walk -- which is exactly the storage whose
    /// stores are all in view here.
    fn place_key(&self, e: &Expr) -> Option<(String, String)> {
        if let Some(p) = self.unalias(e) {
            return self.place_key(&p);
        }
        match &strip_vattr(e).val {
            ExprT::Var(v) if self.slots.iter().any(|s| s.name == *v.val) => {
                Some((v.val.to_string(), String::new()))
            }
            ExprT::Member(base, f) => {
                let (slot, path) = self.place_key(base)?;
                Some((
                    slot,
                    if path.is_empty() {
                        f.val.to_string()
                    } else {
                        format!("{}.{}", path, f.val)
                    },
                ))
            }
            _ => None,
        }
    }

    /// Forget what was known about the code pointers a store overwrites.
    /// Storing a whole struct replaces every field in it, so the whole subtree
    /// under the path goes.
    fn clear_fn_notes(&mut self, lhs: &Expr) {
        let Some((slot, path)) = self.place_key(lhs) else {
            return;
        };
        let Some(i) = self.slots.iter().rposition(|s| s.name == slot) else {
            return;
        };
        if path.is_empty() {
            self.slots[i].holds_fn.clear();
        } else {
            let under = format!("{}.", path);
            self.slots[i]
                .holds_fn
                .retain(|k, _| *k != path && !k.starts_with(&under));
        }
    }

    /// The code pointers a stored value is known to contain, keyed by their
    /// path within it. A brace initialiser is a dispatch table written in one
    /// statement, so its fields are read out here rather than each being a
    /// store of its own.
    fn fn_notes(&self, rhs: &Expr) -> BTreeMap<String, String> {
        let mut out = BTreeMap::new();
        if let Some(g) = self.target_of(rhs) {
            out.insert(String::new(), g);
        }
        if let ExprT::StructInit(_, fields) = &strip_vattr(rhs).val {
            for (f, e) in fields.iter() {
                for (k, g) in self.fn_notes(e) {
                    out.insert(join_path(&f.val.to_string(), &k), g);
                }
            }
        }
        out
    }

    /// Record that a place now holds known functions' addresses.
    fn note_fn_store(&mut self, lhs: &Expr, rhs: &Expr) {
        let Some((slot, path)) = self.place_key(lhs) else {
            return;
        };
        // Whatever the place held before, it holds this now. Copying one
        // pointer into another carries the target across, and a store whose
        // target is not known has to leave the note cleared rather than let
        // the old one stand -- keeping it would be the one way this could go
        // wrong.
        let notes = self.fn_notes(rhs);
        if let Some(i) = self.slots.iter().rposition(|s| s.name == slot) {
            for (k, g) in notes {
                self.slots[i].holds_fn.insert(join_path(&path, &k), g);
            }
        }
    }

    /// The wrapper projections a call through a known function needs.
    fn fp_spec(g: &str) -> (String, String, String) {
        (
            format!("(pre_of func_{}__fp)", g),
            format!("(post_of func_{}__fp)", g),
            format!(
                "(of_fn_div (pre_of func_{g}__fp) (post_of func_{g}__fp) func_{g}__fp)",
                g = g
            ),
        )
    }

    /// The size of what a pointer type points at, when arithmetic on it means
    /// anything: C measures a pointer offset in elements, and the model in
    /// bytes.
    fn elem_size(&self, ty: &Type) -> Option<u64> {
        // `pointee` stops at `_plain`, because that annotation says the
        // translation grants no ownership through the pointer. Arithmetic on
        // it is still arithmetic on a C pointer, and how far one step moves is
        // a question about the type and not about who owns what.
        let pt = match pointee(self.tds, ty) {
            Some(pt) => pt.clone(),
            None => match &peel(self.tds, ty).val {
                TypeT::Pointer(pt, _) => pt.clone(),
                _ => return None,
            },
        };
        palow_sizeof(self.tds, &pt).filter(|n| *n > 0)
    }

    /// An offset in bytes, as a `size_t`, for a subscript-like operand.
    fn byte_offset(&mut self, esize: u64, e: &Expr) -> Result<String, String> {
        // A literal index is settled here, which is both shorter and one less
        // multiplication for the solver to reason about.
        if let Some(k) = const_index(&strip_vattr(e).val) {
            return Ok(format!("{}sz", k * esize));
        }
        let i = self.index(e)?;
        Ok(format!("({}sz `SizeT.mul` {})", esize, i))
    }

    /// Arithmetic and ordering on pointers, which is arithmetic and ordering
    /// on addresses.
    ///
    /// ISO C defines `<`, `<=` and `-` only within a single object, and leaves
    /// an out-of-bounds pointer undefined even if it is never dereferenced.
    /// Palow is more permissive on both counts, for the same reason `( +! )`
    /// is total: forming a pointer is not an access, and it is the access that
    /// the ownership discipline governs.
    ///
    /// Returns `None` when neither operand is a pointer, which leaves the
    /// ordinary integer path alone.
    /// A pointer read purely for its address: compared, subtracted or
    /// offset from. An alias naming an array element normally hands out the
    /// focus that reaches the element, but arithmetic on the address needs no
    /// ownership at all, so the focus is computed for its spelling and then
    /// withdrawn again.
    fn ptr_val(&mut self, e: &Expr) -> Result<String, String> {
        if let Some(v) = lvalue_name(e)
            && self.alias_addr(&v).is_none()
            && let Some(place) = self.aliases.get(&v).cloned()
            && let ExprT::Index(arr, idx) = &strip_vattr(&place).val
            && self.is_array_place(arr)
        {
            let (arr, idx) = (arr.clone(), idx.clone());
            self.uses.insert(v);
            let mark = self.lines.len();
            let f = self.focus_elem(&arr, Some(&idx), false);
            self.lines.truncate(mark);
            return f.map(|f| f.at);
        }
        self.rvalue(e)
    }

    fn ptr_binop(&mut self, op: BinOp, l: &Expr, r: &Expr) -> Result<Option<String>, String> {
        let (lt, rt) = (self.ty_of(l)?, self.ty_of(r)?);
        let lp = self.elem_size(&lt);
        let rp = self.elem_size(&rt);
        if lp.is_none() && rp.is_none() {
            return Ok(None);
        }
        match (op, lp, rp) {
            (BinOp::Add, Some(n), None) => {
                let a = self.ptr_val(l)?;
                let off = self.byte_offset(n, r)?;
                Ok(Some(format!("({} +! {})", a, off)))
            }
            // `n + p` is `p + n`; C says so, and neither side has an effect
            // the other can observe.
            (BinOp::Add, None, Some(n)) => {
                let b = self.ptr_val(r)?;
                let off = self.byte_offset(n, l)?;
                Ok(Some(format!("({} +! {})", b, off)))
            }
            (BinOp::Sub, Some(n), None) => {
                let a = self.ptr_val(l)?;
                let off = self.byte_offset(n, r)?;
                Ok(Some(format!("({} -! {})", a, off)))
            }
            // The difference of two pointers is in elements, and the model
            // works in bytes, so it is a byte difference divided by the
            // element size -- exactly the identity C states.
            (BinOp::Sub, Some(n), Some(_)) => {
                let a = self.ptr_val(l)?;
                let b = self.ptr_val(r)?;
                Ok(Some(format!(
                    "(FStar.Int64.div (ptr_diff {} {}) {}L)",
                    a, b, n
                )))
            }
            (BinOp::Lt, Some(_), Some(_)) => {
                let a = self.ptr_val(l)?;
                let b = self.ptr_val(r)?;
                Ok(Some(format!("({} `ptr_lt` {})", a, b)))
            }
            (BinOp::LEq, Some(_), Some(_)) => {
                let a = self.ptr_val(l)?;
                let b = self.ptr_val(r)?;
                Ok(Some(format!("({} `ptr_le` {})", a, b)))
            }
            // `==` is the model's own decidable equality, which is
            // provenance-sensitive; `binop` already has it.
            _ => Ok(None),
        }
    }

    /// The closed address an alias stands for, if it stands for one. An alias
    /// is normally a name for a *place*, and using it as a value would mean
    /// handing out the focus that reaches the place -- which cannot outlive
    /// the statement. A global is the exception: its address is a constant of
    /// type `ptr`, fixed for the whole run, so there is no focus to hand out
    /// and nothing escapes.
    fn alias_addr(&self, v: &str) -> Option<String> {
        let place = self.aliases.get(v)?;
        let ExprT::Var(g) = &strip_vattr(place).val else {
            return None;
        };
        if self.env.lookup_var(g).is_some() {
            return None;
        }
        self.env.addressable_global(g)?;
        Some(format!("addr_var_{}", g.val))
    }

    /// An initialiser read as a value *at a known type*, which is the one
    /// thing `rvalue` cannot do on its own: `{ 1, 2 }` for `int f[4]` means a
    /// four-element sequence, and only the target type says four. C's rule
    /// that the elements not given are zeroed is applied here, by padding.
    fn init_value(&mut self, ty: &Type, e: &Expr) -> Result<String, String> {
        if flat_array(self.tds, ty).is_none() {
            return self.rvalue(e);
        }
        if !matches!(strip_vattr(e).val, ExprT::ArrayInit { .. }) {
            return self.rvalue(e);
        }
        let mut vs = Vec::new();
        self.init_flat(ty, e, &mut vs)?;
        Ok(format!("(Seq.seq_of_list [{}])", vs.join("; ")))
    }

    /// The leaves of an array initialiser, in storage order. A
    /// multidimensional array is one flat sequence, so `{{1, 2}}` for a
    /// `uint32_t[3][4]` contributes twelve elements and not three rows: the
    /// nesting in the source says where a row ends, and C11 6.7.9p21 says
    /// what fills the rest of it.
    fn init_flat(&mut self, ty: &Type, e: &Expr, out: &mut Vec<String>) -> Result<(), String> {
        let TypeT::FixedArray(elem, n) = &peel(self.tds, ty).val else {
            out.push(self.rvalue(e)?);
            return Ok(());
        };
        let elem = elem.clone();
        let n = usize::try_from(*n).map_err(|_| "an array too long to initialise".to_string())?;
        let ExprT::ArrayInit { elems, .. } = &strip_vattr(e).val else {
            return Err("an array initialised by something that is not a list".to_string());
        };
        if elems.len() > n {
            return Err("an initialiser with more elements than the array".to_string());
        }
        let start = out.len();
        for x in elems {
            self.init_flat(&elem, x, out)?;
        }
        // How many leaves one element of this array is worth, which is the
        // unit the zero padding has to be counted in.
        let (leaf, per) = match flat_array(self.tds, &elem) {
            Some((t, k)) => (t, usize::try_from(k).unwrap_or(1)),
            None => (elem.as_ref(), 1),
        };
        let z = zero_value(self.tds, leaf)?;
        while out.len() < start + n * per {
            out.push(z.clone());
        }
        Ok(())
    }

    fn rvalue(&mut self, e: &Expr) -> Result<String, String> {
        if let Some(p) = self.unalias(e) {
            return self.rvalue(&p);
        }
        if let Some(v) = lvalue_name(e) {
            if let Some(a) = self.alias_addr(&v) {
                self.uses.insert(v.clone());
                return Ok(a);
            }
            // The value of an alias is the address of the place it stands
            // for, and an address is not ownership: nothing is read by taking
            // one and no focus is opened, so handing it out costs nothing.
            // Whoever accesses through it still has to have the ownership,
            // which is where the obligation belongs.
            if let Some(place) = self.aliases.get(&v).cloned() {
                self.uses.insert(v.clone());
                return self.addr(&place);
            }
        }
        match &e.val {
            ExprT::VAttr(_, inner) => self.rvalue(inner),
            // A string or compound literal used as a value is an object with
            // static storage duration, and what the expression denotes is its
            // address. There is no ownership to produce and no scope to free
            // it at: the address is the whole of it.
            ExprT::ArrayInit { elems, .. } => {
                let ty = self.ty_of(e)?;
                let TypeT::FixedArray(elem, _) = &peel(self.tds, &ty).val else {
                    return Err("an initialiser list is not translated yet".to_string());
                };
                let elem = elem.clone();
                let mut vs = Vec::new();
                for x in elems {
                    vs.push(self.init_value(&elem, x)?);
                }
                Ok(format!(
                    "(Pulse.Lib.C.Palow.Ptr.literal_addr [{}])",
                    vs.join("; ")
                ))
            }
            // C says the value of an assignment is the value stored, after
            // the conversion to the left operand's type -- which elaboration
            // has already inserted, so the stored expression is the answer.
            ExprT::AssignExpr(lhs, rhs) => {
                let ty = self.ty_of(lhs)?;
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("an assignment to {}", describe(&ty)))?;
                let v = self.rvalue(rhs)?;
                self.store(lhs, &pn, &v)?;
                self.note_fn_store(lhs, rhs);
                Ok(v)
            }
            ExprT::Var(v) => {
                if let Some(s) = self.slots.iter().rev().find(|s| s.name == *v.val) {
                    if !s.init {
                        return Err(format!("`{}` is read before it is written", v.val));
                    }
                    let ty = self.ty_of(e)?;
                    if !readable_field(self.tds, &ty) {
                        return Err(format!(
                            "a whole-value read of `{}`, which is {}",
                            v.val,
                            describe(self.tds.resolve(&ty))
                        ));
                    }
                    let pn = palow_name(self.tds, &ty)
                        .ok_or_else(|| format!("`{}` has an unsupported type", v.val))?;
                    let a = s.addr.clone();
                    let t = self.fresh(&v.val);
                    self.lines.push(format!("let {} = {}_read {};", t, pn, a));
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
                        let f = self.focus_elem(inner, None, false)?;
                        self.lines.extend(f.open_read.iter().cloned());
                        let t = self.fresh("elem");
                        self.lines
                            .push(format!("let {} = {}_read {};", t, f.pn, f.at));
                        self.lines.extend(f.close_read);
                        return Ok(t);
                    }
                }
                let ty = self.ty_of(e)?;
                if !readable_field(self.tds, &ty) {
                    return Err(format!(
                        "a whole-value read of {}",
                        describe(self.tds.resolve(&ty))
                    ));
                }
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("a dereference yields {}", describe(&ty)))?;
                let a = self.addr(e)?;
                let t = self.fresh("deref");
                self.lines.push(format!("let {} = {}_read {};", t, pn, a));
                Ok(t)
            }
            // A subscript of a published array global is `Seq.index` of a
            // constant. There is no read to sequence and nothing to own, so it
            // is a term like any other -- which is also what lets it appear in
            // an assertion.
            ExprT::Index(base, idx)
                if matches!(&strip_vattr(base).val,
                            ExprT::Var(v) if self.slots.iter().all(|s| s.name != *v.val)
                                && self.global_array_value(v)) =>
            {
                let ExprT::Var(v) = &strip_vattr(base).val else {
                    unreachable!()
                };
                // A constant index is settled at translation time, and folding
                // it saves the solver from walking the list one cons at a
                // time, which is what decides whether a large table is
                // affordable.
                if let Some(x) = self.const_read(e) {
                    return Ok(x);
                }
                // The length is in the type, so a constant index carries its
                // own bound. Anything else needs the function's `_requires`,
                // and emitting it without one produces a failure about the
                // subscript rather than about the memory model.
                let n = self.global_array_len(v).unwrap_or(0);
                let literal = const_index(&strip_vattr(idx).val).is_some_and(|k| k < n);
                if !literal && !self.signed_ok {
                    return Err(format!(
                        "a subscript of `{}`, whose bounds obligation needs the untranslated \
                         `_requires`",
                        v.val
                    ));
                }
                let i = self.rvalue(idx)?;
                Ok(format!("(Seq.index var_{} (SizeT.v {}))", v.val, i))
            }
            ExprT::Member(..) | ExprT::Index(..) => {
                // A path into a global nothing can write is settled at
                // translation time, so it is a term rather than a read: no
                // ownership, no sequencing, and usable inside an assertion.
                if let Some(x) = self.const_read(e) {
                    return Ok(x);
                }
                // A path into a parameter passed by value is a projection out
                // of a record this function already holds, not a read of
                // memory.
                if let Some(x) = self.value_read(e) {
                    return Ok(x);
                }
                // A subscript of a constant table whose index is not itself a
                // constant. The table is a closed term, so the read is
                // `Seq.index` of it -- no ownership, no sequencing, and
                // usable inside an assertion, exactly like the scalar case
                // above. `const_seq_with_len` keeps that affordable: its
                // length and its indexing are SMT patterns, so the solver
                // never walks the list.
                if let ExprT::Index(base, idx) = &e.val
                    && let Some((bty, Some(binit))) = self.const_path(base)
                    && let Some((_, n, term)) = const_array(self.tds, &bty, &binit)
                {
                    let literal = const_index(&strip_vattr(idx).val).is_some_and(|k| k < n);
                    if !literal && !self.signed_ok {
                        return Err("a subscript of a constant table, whose bounds obligation \
                                    needs the untranslated `_requires`"
                            .to_string());
                    }
                    let i = self.rvalue(idx)?;
                    return Ok(format!("(Seq.index {} (SizeT.v {}))", term, i));
                }
                // A field whose type is an array decays to a pointer to its
                // first element, exactly as a whole array does, and Palow
                // names that pointer by the field's address. Nothing is read
                // and no ownership changes hands by taking one: whoever
                // accesses through it still has to focus the field out of the
                // struct, which is where the obligation belongs.
                if let ExprT::Member(base, f) = &e.val {
                    let fty = self.field_ty(base, f)?;
                    if matches!(peel(self.tds, &fty).val, TypeT::FixedArray(..)) {
                        return self.addr(e);
                    }
                }
                // A compound literal is an lvalue in C, but it is one with no
                // storage a program can name, and C code reads a field out of
                // one the moment a named constant is written as a macro. In
                // Palow a structure is a record value, so the read is the
                // projection: no address, no ownership, and nothing to focus.
                if let ExprT::Member(base, f) = &e.val
                    && matches!(&strip_vattr(base).val, ExprT::StructInit(..))
                {
                    // The literal is a record with no type of its own, so the
                    // projection has to say which record it is.
                    let bty = self.ty_of(base)?;
                    let pn = palow_name(self.tds, &bty)
                        .ok_or_else(|| format!("a field of {}", describe(&bty)))?;
                    let v = self.rvalue(base)?;
                    return Ok(format!("(({} <: {}).fld_{})", v, pn, f.val));
                }
                let hint = match &e.val {
                    ExprT::Member(_, f) => f.val.to_string(),
                    _ => "elem".to_string(),
                };
                let f = self.place(e, false)?;
                self.lines.extend(f.open_read.iter().cloned());
                let t = self.fresh(&hint);
                self.lines
                    .push(format!("let {} = {}_read {};", t, f.pn, f.at));
                self.lines.extend(f.close_read);
                // A bit-field has no storage of its own, so the read reads
                // the unit and the bits come out of the value. This is also
                // what the C compiler does, and why `s->a` is not an lvalue
                // an address can be taken of.
                let Some(pos) = f.bits else {
                    return Ok(t);
                };
                let v = self.fresh(&hint);
                self.lines.push(format!("let {} = {};", v, pos.get(&t)));
                Ok(v)
            }
            ExprT::BoolLit(b) => Ok(if *b { "true" } else { "false" }.to_string()),
            // A brace initialiser is a value, not a sequence of writes: the
            // generated type is a record, so `{ .x = 1 }` is that record with
            // the named fields given and the rest zeroed, which is what C says
            // an incomplete initialiser means. Zeroing is a real translation
            // rather than a guess -- `zero_value` builds the zero of the
            // field's type, which for a nested struct is its own zeroed
            // record -- so a partial initialiser needs no special case.
            ExprT::StructInit(n, inits) => {
                let Some(si) = self.tds.structs.get(&*n.val) else {
                    return Err(format!("an initialiser for struct {}", n.val));
                };
                let names: Vec<(String, Rc<Type>)> = si
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), f.ty.clone()))
                    .collect();
                let mut vals = Vec::new();
                for (fname, fty) in names {
                    let given = inits.iter().find(|(i, _)| *i.val == *fname);
                    let v = match given {
                        Some((_, e)) => self.init_value(&fty, e)?,
                        None => zero_value(self.tds, &fty)?,
                    };
                    vals.push(format!("fld_{} = {}", fname, v));
                }
                Ok(format!("({{ {} }})", vals.join("; ")))
            }
            // A union initialiser names exactly one member, and that is the
            // member the value is tagged with -- which is the same thing C
            // means by it becoming the live one.
            ExprT::UnionInit(n, m, e) => {
                if !self.tds.unions.contains_key(&*n.val) {
                    return Err(format!("an initialiser for union {}", n.val));
                }
                let v = self.rvalue(e)?;
                Ok(format!("(Union_{}_{} {})", n.val, m.val, v))
            }
            ExprT::IntLit(n, ty) => int_literal(self.tds, n, ty),
            ExprT::FloatLit(text, ty) => float_literal(self.tds, text, ty),
            ExprT::Cast(inner, to) => {
                let from = self.ty_of(inner)?;
                // An array in an rvalue context is its first element's
                // address: C's decay, which clang has already made explicit as
                // this cast. What the address carries is the other half. A
                // local array is held in the `option` view, because its
                // elements are written one at a time, and a callee taking
                // `T *` asks for the plain one -- so the conversion happens
                // here, and the way back is owed until the statement is done.
                if let (TypeT::FixedArray(..), TypeT::Pointer { .. }) =
                    (&self.tds.resolve(&from).val, &self.tds.resolve(to).val)
                {
                    if let Some(v) = lvalue_name(inner) {
                        if let Some(sl) = self.slots.iter().rev().find(|s| s.name == v) {
                            if let Some((esize, maybe)) = sl.array.clone() {
                                let (addr, pn) = (sl.addr.clone(), sl.palow_ty.clone());
                                if maybe {
                                    self.lines.push(format!(
                                        "array_somes {}_repr {} {};",
                                        pn, addr, esize
                                    ));
                                    self.pending_close.push(format!(
                                        "array_unsomes {}_repr {} {};",
                                        pn, addr, esize
                                    ));
                                }
                                return Ok(addr);
                            }
                        }
                    }
                }
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
                if let Some(x) = self.ptr_binop(*op, l, r)? {
                    return Ok(x);
                }
                let ty = self.ty_of(l)?;
                let opstr = binop(self.tds, *op, &ty, self.signed_ok)?;
                let a = self.rvalue(l)?;
                let b = self.rvalue(r)?;
                Ok(format!("({} {} {})", a, opstr, b))
            }
            // `x++` is a read, an add and a write. The old value has to be
            // bound before the write, because after it there is nowhere left
            // to read it from -- and that is also what makes the post- forms
            // work, since they are the ones that return it.
            ExprT::PreIncr(x) | ExprT::PostIncr(x) | ExprT::PreDecr(x) | ExprT::PostDecr(x) => {
                let post = matches!(&e.val, ExprT::PostIncr(..) | ExprT::PostDecr(..));
                let op = match &e.val {
                    ExprT::PreIncr(..) | ExprT::PostIncr(..) => BinOp::Add,
                    _ => BinOp::Sub,
                };
                let ty = self.ty_of(x)?;
                // Incrementing a pointer moves it by one *element*, so the
                // step is the element's size rather than one.
                if let Some(esize) = self.elem_size(&ty) {
                    let cur = self.rvalue(x)?;
                    let old = self.fresh("old");
                    self.lines.push(format!("let {} = {};", old, cur));
                    let new = match op {
                        BinOp::Add => format!("({} +! {}sz)", old, esize),
                        _ => format!("({} -! {}sz)", old, esize),
                    };
                    self.store(x, "ptr", &new)?;
                    return Ok(if post { old } else { new });
                }
                let one = match &peel(self.tds, &ty).val {
                    TypeT::Int { signed, width } => format!("1{}", int_suffix(*signed, *width)?),
                    TypeT::SizeT => "1sz".to_string(),
                    _ => return Err(format!("an increment of {}", describe(&ty))),
                };
                let opstr = binop(self.tds, op, &ty, self.signed_ok)?;
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("an increment of {}", describe(&ty)))?;
                let cur = self.rvalue(x)?;
                let old = self.fresh("old");
                self.lines.push(format!("let {} = {};", old, cur));
                let new = format!("({} {} {})", old, opstr, one);
                self.store(x, &pn, &new)?;
                Ok(if post { old } else { new })
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
                    // C's unary minus on a float flips the sign bit and has no
                    // obligation attached; `0 - x` is the same value for every
                    // input but one, and `-0.0` is not a value this program
                    // can tell apart from `0.0` without `bit_eq`.
                    TypeT::Float { .. } => {
                        let m = float_mod(self.tds, &ty)
                            .ok_or_else(|| format!("a negation of {}", describe(&ty)))?;
                        Ok(format!("({}.sub {}.zero {})", m, m, a))
                    }
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
                _ => self.addr_only(inner),
            },
            ExprT::FnCall(name, args) if self.tds.pure_fns.contains(&*name.val.to_string()) => {
                let mut out = format!("func_{}", name.val);
                for a in args.iter() {
                    // A `_let` function may take a specification integer,
                    // which has no machine representation to produce -- the
                    // argument is a mathematical value, so it is translated
                    // as one.
                    let spec_arg = self.ty_of(a).is_ok_and(|t| {
                        matches!(self.tds.resolve(&t).val, TypeT::SpecInt | TypeT::SpecNat)
                    });
                    let v = if spec_arg {
                        self.num(a)?
                    } else {
                        self.rvalue(a)?
                    };
                    out += &format!(" {}", v);
                }
                if args.is_empty() {
                    out += " ()";
                }
                Ok(format!("({})", out))
            }
            ExprT::FnCall(name, args) => {
                let t = self.fresh(&name.val);
                let mark = self.seeded.len();
                let call = self.call(name, args)?;
                self.lines.push(format!("let {} = {};", t, call));
                // A validity seeded while evaluating the arguments was seeded
                // for this call. The callee hands it back -- it is a fact, not
                // a resource anyone consumes -- so it has to be put down here
                // or it is left over at the end of the body.
                self.drop_seeded(mark);
                Ok(t)
            }
            // A named function used as a value is its code address. Because
            // a function pointer is just a `ptr`, nothing has to be encoded:
            // the value is the `of_fn_div` of the wrapper, and what it
            // satisfies is recovered from the wrapper's type by `pre_of` and
            // `post_of` rather than named separately.
            ExprT::FnRef(g) => {
                let name = g.val.to_string();
                let c = self
                    .callees
                    .get(&name)
                    .ok_or_else(|| format!("`{}` is not declared in this file", g.val))?;
                if !c.fp {
                    return Err(format!("`{}` has no function-pointer wrapper", g.val));
                }
                if self.forbidden.contains(&name) {
                    return Err(format!("`{}`, which is recursive", g.val));
                }
                self.uses.insert(name);
                // Seed the validity here rather than leaving it to the caller.
                // It is a ghost step producing a `pure` fact, so it costs
                // nothing and cannot be wrong, and it is what lets a decayed
                // function be passed straight to a callback parameter without
                // the `_ghost_stmt` the old translator needs.
                let (pre, post, addr) = Self::fp_spec(&g.val);
                self.lines.push(format!(
                    "of_fn_div_valid {} {} func_{}__fp;",
                    pre, post, g.val
                ));
                self.seeded
                    .push((addr.clone(), pre.clone(), post.clone(), g.val.to_string()));
                Ok(addr)
            }
            // An indirect call needs the `valid` fact, which no points-to
            // carries: the bytes of a code pointer say where the code is, not
            // what it does. Where the emitter knows which function the pointer
            // holds it can seed validity itself, from the wrapper, and the
            // `_ghost_stmt` the existing translator needs disappears. The
            // address passed is the decay rather than a load of the slot,
            // which is the same value -- that is what knowing the store means
            // -- and keeps `is_valid` and the callee syntactically the same
            // term, since slprop matching will not do the reasoning.
            ExprT::FnPtrCall(f, args) => {
                // A pointer whose target the emitter does not know is still
                // callable if the contract said what the code at it does.
                // `is_valid` is the only thing that can say so, and the
                // pre/post are left to slprop matching: the fact in context is
                // the author's, written in their own words, and naming them
                // here would mean parsing those words.
                if let Some(base) = fp_base(f)
                    && self.target_of(f).is_none()
                    && (self.valid_fps.contains(&base) || self.local_valid_fps.contains(&base))
                {
                    // The pointer itself, when the contract named it, and
                    // otherwise a load of the field holding it. A load is
                    // the identity on the state and comes with a
                    // `rewrites_to`, so the address handed to `call_div` is
                    // the same term the `is_valid` in context is stated at --
                    // which is what makes slprop matching find it.
                    let callee = match &strip_vattr(f).val {
                        ExprT::Var(v) if self.params.contains(&v.val.to_string()) => {
                            format!("var_{}", v.val)
                        }
                        _ => self.rvalue(f)?,
                    };
                    let mut vs = Vec::new();
                    for a in args.iter() {
                        vs.push(self.rvalue(a)?);
                    }
                    let tuple = match vs.len() {
                        0 => "()".to_string(),
                        1 => vs[0].clone(),
                        _ => format!("({})", vs.join(", ")),
                    };
                    self.divergent = true;
                    let t = self.fresh(&base);
                    // The witness the callee's wrapper takes is decided by
                    // its parameters, and a function-pointer type says what
                    // those are: a parameter with a pointee contributes the
                    // value the callee owns at it, and one without
                    // contributes nothing.
                    let fty = self.ty_of(f)?;
                    let nwit = match &peel(self.tds, &fty).val {
                        TypeT::FnPtr { args, .. } => args
                            .iter()
                            .filter(|a| pointee(self.tds, a).is_some())
                            .count(),
                        _ => 0,
                    };
                    self.lines.push(format!(
                        "let {} = call_div _ _ {} {} {};",
                        t,
                        callee,
                        tuple,
                        witness_holes(nwit)
                    ));
                    // The callee hands the validity back -- it is a fact, not
                    // a resource it uses up. Where the caller keeps the
                    // ownership it came with, the fact goes back into the
                    // postcondition along with it; where the caller handed
                    // that ownership over for good, nothing wants it and it
                    // has to be put down or it is left over at the end.
                    if self.consumed.contains(&base) {
                        self.lines.push("drop_is_valid _ _ _;".to_string());
                    }
                    return Ok(t);
                }
                let g = self.target_of(f).ok_or_else(|| match &strip_vattr(f).val {
                    ExprT::Var(v) => {
                        format!("a call through `{}`, whose target is not known here", v.val)
                    }
                    _ => "a call through a function pointer".to_string(),
                })?;
                if !self.callees.get(&g).is_some_and(|c| c.fp) {
                    return Err(format!("`{}` has no function-pointer wrapper", g));
                }
                self.uses.insert(g.clone());
                let mut vs = Vec::new();
                for a in args.iter() {
                    vs.push(self.rvalue(a)?);
                }
                let tuple = match vs.len() {
                    0 => "()".to_string(),
                    1 => vs[0].clone(),
                    _ => format!("({})", vs.join(", ")),
                };
                // The wrapper's witness has one component per implicit its
                // contract quantifies, and the emitter built that wrapper, so
                // it knows how many. Which values they are is left to slprop
                // matching against the ownership being handed over.
                let w = witness_holes(self.callees.get(&g).map_or(0, |c| c.fp_wits));
                let (pre, post, addr) = Self::fp_spec(&g);
                // `call_div` lives in the divergent effect, so its caller does
                // too -- which every PAL function that is not `_total` already
                // is.
                self.divergent = true;
                self.lines
                    .push(format!("of_fn_div_valid {} {} func_{}__fp;", pre, post, g));
                let t = self.fresh(&g);
                self.lines.push(format!(
                    "let {} = call_div {} {} {} {} {};",
                    t, pre, post, addr, tuple, w
                ));
                self.lines
                    .push(format!("drop_is_valid {} {} {};", addr, pre, post));
                Ok(t)
            }
            // `_container_of` recovers the enclosing structure from a pointer
            // to one of its fields. In the old model that was a generated
            // projection with a pair of round-trip lemmas, because a `ref` to
            // a field was a different kind of thing from a `ref` to the
            // struct. Here both are addresses, so it is a subtraction, and the
            // round trip is `add_sub_wrap`: a caller who knows the field
            // pointer came from a structure knows it as `base +! offset`, and
            // that is exactly the form the lemma fires on.
            ExprT::ContainerOf(inner, ty, field) => {
                let TypeT::TypeRef(TypeRefKind::Struct(sname)) = &self.tds.resolve(ty).val else {
                    return Err(format!(
                        "`_container_of` of {}",
                        describe(self.tds.resolve(ty))
                    ));
                };
                if !self.tds.structs.contains_key(&*sname.val) {
                    return Err(format!(
                        "`_container_of` of {}",
                        describe(self.tds.resolve(ty))
                    ));
                }
                let base = self.rvalue(inner)?;
                Ok(sub_offset(
                    base,
                    &format!("struct_{}_offsetof_{}", sname.val, field.val),
                ))
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
        // A callee that was handed a pointer may have made a different member
        // live, and nothing in the signature says otherwise. The emitter's
        // record of which member is live is knowledge it put there itself, so
        // it gives it up whenever control leaves.
        self.active.clear();
        let c = self
            .callees
            .get(&*name.val.to_string())
            .ok_or_else(|| format!("`{}` is not declared in this file", name.val))?;
        if self.forbidden.contains(&*name.val.to_string())
            && self.self_rec.as_deref() != Some(&*name.val.to_string())
        {
            return Err(format!("`{}`, which is recursive", name.val));
        }
        self.uses.insert(name.val.to_string());
        // Divergence is contagious: calling a function that may not terminate
        // makes this one a function that may not terminate.
        if self.divergent_fns.contains(&*name.val.to_string()) {
            self.divergent = true;
        }
        if let Err(why) = c.simple {
            return Err(format!("`{}` {}", name.val, why));
        }
        if !c.contract && self.has_contract {
            return Err(format!("`{}`'s contract was dropped", name.val));
        }
        let outs = c.outs.clone();
        let plain_ptrs = c.plain_ptrs.clone();
        let arr_args = c.arr_args.clone();
        let consumes = c.consumes.clone();
        let mut out = format!("func_{}", name.val);
        for (i, a) in args.iter().enumerate() {
            // A literal's address carries nothing, so a parameter that wants
            // ownership -- an `_array`, or any pointer that is not `_plain` --
            // cannot be handed one. Saying so here rather than emitting the
            // address keeps the refusal visible instead of leaving F* to fail
            // on a missing points-to.
            // The array behind a *pointer field* is owned by the struct's
            // deep predicate, so handing it to a callee means unfolding that
            // predicate for the length of the statement -- the same borrow a
            // dereference through such a field already takes, and put back by
            // the same gather. Where the field is not one the contract owns
            // deeply there is nothing to unfold and the call is refused,
            // rather than left to F* to fail on a points-to that was never
            // granted.
            if arr_args.get(i) == Some(&true)
                && outs.get(i) != Some(&true)
                && let ExprT::Member(..) = &strip_vattr(a).val
                && let Ok(aty) = self.ty_of(a)
                && matches!(peel(self.tds, &aty).val, TypeT::Pointer(..))
            {
                match self.own_item(a) {
                    Some((pv, sn, _)) => self.open_own(&pv, &sn),
                    // Nothing in the generated model owns it -- but a
                    // contract that spliced its own ownership in may, and the
                    // emitter cannot read those words. It says nothing and
                    // lets slprop matching decide.
                    None if self.spliced_own => {}
                    None => {
                        return Err(
                            "an array behind a struct field, whose ownership the contract does \
                             not state"
                                .to_string(),
                        );
                    }
                }
            }
            // A `calloc`ed extent is in the uninitialised view -- every cell
            // a `Some`, but a `Some` all the same -- and a callee that takes
            // an ordinary array wants the other one. The values are known, so
            // the claim is exact: nothing is assumed about what is there, only
            // that zeros are what the allocator promised.
            if arr_args.get(i) == Some(&true)
                && outs.get(i) != Some(&true)
                && let ExprT::Var(v) = &strip_casts(a).val
                && let Some(bi) = self.blocks.iter().position(|b| {
                    b.var == *v.val.to_string()
                        && b.checked
                        && !b.freed
                        && b.array
                            .as_ref()
                            .is_some_and(|x| !x.filled && x.zero.is_some())
                })
            {
                let (pn, tmp) = (self.blocks[bi].pn.clone(), self.blocks[bi].tmp.clone());
                let ab = self.blocks[bi].array.clone().unwrap();
                let (z, _) = ab.zero.clone().unwrap();
                self.lines.push(format!(
                    "array_claim_all {}_repr {} {} (Seq.create (SizeT.v {}) {});",
                    pn, tmp, ab.esize, ab.n, z
                ));
                if let Some(x) = self.blocks[bi].array.as_mut() {
                    x.filled = true;
                }
            }
            // An *inline* array field is different: the elements are inside
            // the struct, so what the callee needs is not a separate
            // ownership to unfold but a view of part of this object. That is
            // the field focus, held open for the statement and given back by
            // the same unfocus a write through the field would use -- the
            // callee may have changed the elements, which is exactly what the
            // implicit value argument is for.
            if arr_args.get(i) == Some(&true)
                && outs.get(i) != Some(&true)
                && let ExprT::Member(base, f) = &strip_casts(a).val
                && let Ok(aty) = self.ty_of(strip_casts(a))
                && matches!(peel(self.tds, &aty).val, TypeT::FixedArray(..))
            {
                let (sn, _) = self.struct_of(base)?;
                let at = self.addr_only(base)?;
                self.lines.push(format!("{}_focus_{} {};", sn, f.val, at));
                self.pending_close
                    .push(format!("{}_unfocus_{} {};", sn, f.val, at));
            }
            let v = if outs.get(i) == Some(&true) {
                self.out_arg(a)?
            } else if is_literal(a) && plain_ptrs.get(i) != Some(&true) {
                self.literal_arg(a)?
            } else {
                self.rvalue(a)?
            };
            // A `_consumes` parameter takes the argument's ownership for good.
            // Nothing has to be emitted for that -- the callee's `requires`
            // asks for it and slprop matching hands it over -- but the
            // caller's own accounting has to stop, or it would go on believing
            // it could read the object, or free it a second time.
            if consumes.get(i) == Some(&true) {
                self.give_away(a)?;
            }
            // Passing the address of an object that holds a code pointer
            // hands the validity along with it.
            if let Some(slot) = self.slots.iter().find(|s| s.addr == v) {
                let held: Vec<String> = slot.holds_fn.values().cloned().collect();
                self.laundered.extend(held);
            }
            out += &format!(" {}", v);
        }
        if args.is_empty() {
            out += " ()";
        }
        Ok(format!("({})", out))
    }

    /// Stop accounting for an object whose ownership a `_consumes` parameter
    /// just took.
    ///
    /// The ownership itself needs no statement -- it is matched out of the
    /// context by the callee's `requires` -- but everything the emitter
    /// remembers about the object is now false: a tracked block is gone, and a
    /// `_consumes` parameter of this function has been passed on and may not
    /// be freed here as well. An argument the emitter was not tracking is
    /// simply ownership the contract granted, and giving it away is what the
    /// call is for.
    fn give_away(&mut self, a: &Expr) -> Result<(), String> {
        let target = self.unalias(a);
        let Some(name) = lvalue_name(target.as_deref().unwrap_or(a)) else {
            // Not a name: an ownership-carrying argument that is not an object
            // this body can stop tracking, because it never started.
            return Ok(());
        };
        if self.freeables.contains_key(&name) && !self.consumed_freed.insert(name.clone()) {
            return Err(format!("`{}`, already given up, passed on", name));
        }
        if let Some(b) = self.blocks.iter_mut().find(|b| b.var == name && !b.freed) {
            b.freed = true;
        }
        Ok(())
    }

    /// The storage passed for an `_out` parameter.
    ///
    /// An `_out` argument is the one place where a call is handed a place
    /// rather than a value, so it is not evaluated: `&x` is storage, and what
    /// the callee wants is the uninitialised points-to. The two things that
    /// can supply one are a local that has not been written and the caller's
    /// own `_out` parameter, and the emitter already tracks both -- so all
    /// this does is spend one and record that it is now initialised.
    fn out_arg(&mut self, a: &Expr) -> Result<String, String> {
        if let ExprT::Ref(inner) = &strip_vattr(a).val
            && let ExprT::Var(v) = &strip_vattr(inner).val
            && let Some(i) = self.slots.iter().rposition(|s| s.name == *v.val)
        {
            // C's `_out` says the callee writes the object, not that the
            // object was never written before. Palow's contract asks for the
            // write-only view, so one that already holds a value gives that
            // value up first -- the same step a local takes on its way to
            // `_stack_free`, and a loss of knowledge rather than of ownership.
            if self.slots[i].init {
                if self.slots[i].array.is_some() {
                    return Err(format!("`&{}`, an array, for an `_out` parameter", v.val));
                }
                let (pn, at) = (self.slots[i].palow_ty.clone(), self.slots[i].addr.clone());
                self.lines.push(format!("{}_forget {};", pn, at));
            }
            self.slots[i].init = true;
            return Ok(self.slots[i].addr.clone());
        }
        // A local array decays to its own address, and its storage view is
        // already the `option` one the callee asks for, so handing it over
        // costs nothing going in. It does cost a step coming back: the callee
        // returns the array full, and the slot has to be released in the view
        // it was allocated with.
        if let ExprT::Cast(inner, _) = &strip_vattr(a).val
            && let Some(v) = lvalue_name(inner)
            && let Ok(fty) = self.ty_of(inner)
            && matches!(peel(self.tds, &fty).val, TypeT::FixedArray(..))
            && let Some(i) = self.slots.iter().rposition(|s| s.name == v)
            && let Some((esize, true)) = self.slots[i].array.clone()
        {
            let (pn, at) = (self.slots[i].palow_ty.clone(), self.slots[i].addr.clone());
            self.pending_close
                .push(format!("array_unsomes {}_repr {} {};", pn, at, esize));
            return Ok(at);
        }
        // An array parameter this function holds a *value* for, handed on as
        // storage. Giving up what is in it is all that is needed going in --
        // the callee promises to fill it again, so the plain view it returns
        // is the one this function goes on holding.
        if let ExprT::Var(v) = &strip_vattr(a).val
            && !self.out_params.iter().any(|n| *n == *v.val)
            && let Some(ap) = self.arrays.get(&*v.val)
            && !ap.maybe
        {
            let (pn, at, esize) = (ap.pn.clone(), ap.addr.clone(), ap.esize.clone());
            self.lines
                .push(format!("array_unsomes {}_repr {} {};", pn, at, esize));
            return Ok(at);
        }
        if let ExprT::Var(v) = &strip_vattr(a).val
            && let Some(i) = self.out_params.iter().position(|n| *n == *v.val)
        {
            self.out_params.remove(i);
            // Dropping it from `out_params` is also what records that the
            // callee filled it: the array leaves in the plain view, so this
            // function has nothing left to prove about it on the way out.
            return Ok(format!("var_{}", v.val));
        }
        // A place rather than a whole object: a field, an array element, or an
        // element of a field's array. The callee writes through it, so it is
        // opened for the length of the statement and closed afterwards, and
        // opening gives back whatever view the place has -- so one that
        // already holds a value gives it up first, which is the same step a
        // written local takes on its way to an `_out` parameter.
        if let Some(p) = self.out_place(a) {
            let f = self.place(&p, true)?;
            self.lines.extend(f.open_write.iter().cloned());
            if f.write_fn == format!("{}_write", f.pn) {
                self.lines.push(format!("{}_forget {};", f.pn, f.at));
            }
            self.pending_close.extend(f.close_write);
            return Ok(f.at);
        }
        Err("an `_out` argument that is not unwritten storage here".to_string())
    }

    /// Give an anonymous array literal storage. C makes a compound literal an
    /// lvalue with automatic storage, and a string literal passed to a
    /// function is exactly that -- so the translation is the one a declared
    /// local array already gets: allocate it, write the elements, and let it
    /// be freed with the rest. The name is invented here because C never gave
    /// it one.
    fn array_literal(&mut self, e: &Expr) -> Result<String, String> {
        let ty = self.ty_of(e)?;
        let TypeT::FixedArray(_, n) = &self.tds.resolve(&ty).val else {
            return Err("an array literal of no fixed length".to_string());
        };
        let ExprT::ArrayInit { elems, .. } = &strip_vattr(e).val else {
            return Err("an array literal that is not an initialiser".to_string());
        };
        if elems.len() as u64 != *n {
            return Err("an array initialiser of another length".to_string());
        }
        self.tmp += 1;
        let name: Rc<IdentT> = Rc::from(format!("lit{}", self.tmp).as_str());
        let id: Rc<Ident> = name.clone().with_loc(e.loc.clone());
        self.env
            .push_var_decl(&id, ty.clone(), crate::env::LocalDeclKind::LValue);
        self.alloc_slot(&id, &ty)?;
        let elems = elems.clone();
        let base = ExprT::Var(id).with_loc(e.loc.clone());
        for (i, x) in elems.iter().enumerate() {
            let idx = ExprT::IntLit(
                Rc::new(BigInt::from(i)),
                TypeT::SizeT.with_loc(e.loc.clone()),
            )
            .with_loc(e.loc.clone());
            let at = ExprT::Index(base.clone(), idx).with_loc(e.loc.clone());
            let st = StmtT::Assign(at, x.clone()).with_loc(e.loc.clone());
            self.stmt(&st)?;
        }
        Ok(name.to_string())
    }

    /// A literal handed to a parameter that wants ownership. A `_plain`
    /// pointer is content with the literal's address and nothing else, which
    /// is what `literal_addr` gives it; anything else -- an `_array`
    /// parameter, above all -- asks for the elements, and the only thing that
    /// can hand those over is storage. So the literal gets some.
    fn literal_arg(&mut self, a: &Expr) -> Result<String, String> {
        let mut lit = Rc::new(strip_vattr(a).clone());
        while let ExprT::Cast(inner, _) = &lit.clone().val {
            lit = Rc::new(strip_vattr(inner).clone());
        }
        let v = self.array_literal(&lit)?;
        let Some(sl) = self.slots.iter().rev().find(|s| s.name == v) else {
            return Err("an initialiser list is not translated yet".to_string());
        };
        let (addr, pn) = (sl.addr.clone(), sl.palow_ty.clone());
        let Some((esize, maybe)) = sl.array.clone() else {
            return Err("an initialiser list is not translated yet".to_string());
        };
        if maybe {
            self.lines
                .push(format!("array_somes {}_repr {} {};", pn, addr, esize));
            self.pending_close
                .push(format!("array_unsomes {}_repr {} {};", pn, addr, esize));
        }
        Ok(addr)
    }

    fn alloc_slot(&mut self, name: &Ident, ty: &Type) -> Result<String, String> {
        // A fixed-size array local is `n` elements of storage written one at
        // a time, so it is owned as an `array_pts_to` whose elements are
        // `option`s. Nothing tracks which of them have been written: the
        // sequence does, and a read of one that has not is a proof obligation
        // the generated code fails rather than something refused here.
        if let TypeT::FixedArray(elem, n) = &self.tds.resolve(ty).val {
            let (Some(pn), Some(esize), Some(ety)) = (
                palow_name(self.tds, elem),
                palow_sizeof(self.tds, elem),
                fstar_type(self.tds, elem),
            ) else {
                return Err(format!(
                    "local `{}` is an array of {}",
                    name.val,
                    describe(self.tds.resolve(elem))
                ));
            };
            if !has_repr(self.tds, elem) {
                return Err(format!(
                    "local `{}` is an array of {}",
                    name.val,
                    describe(self.tds.resolve(elem))
                ));
            }
            self.lines.push(format!(
                "let loc_{} = array_stack_alloc {}_repr {}sz {}sz {}sz;",
                name.val,
                pn,
                esize,
                n,
                esize * n
            ));
            self.slots.push(Slot {
                name: name.val.to_string(),
                addr: format!("loc_{}", name.val),
                palow_ty: pn.clone(),
                // The length is part of the binder's type so that a loop
                // invariant does not have to restate it.
                fstar_ty: format!("(s: Seq.seq (option {}) {{ Seq.length s == {} }})", ety, n),
                init: true,
                array: Some((format!("{}sz", esize), true)),
                global: false,
                union_arm: None,
                filling: None,
                holds_fn: BTreeMap::new(),
                scattered: BTreeSet::new(),
            });
            return Ok(pn);
        }
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
            addr: format!("loc_{}", name.val),
            palow_ty: pn.clone(),
            fstar_ty: fstar_type(self.tds, ty)
                .ok_or_else(|| format!("local `{}` has no F* type", name.val))?,
            init: false,
            array: None,
            global: false,
            union_arm: None,
            filling: None,
            holds_fn: BTreeMap::new(),
            scattered: BTreeSet::new(),
        });
        Ok(pn)
    }

    /// The `unless_null` payload of an allocation: the block's bytes and the
    /// right to give them back. It has to be written out in full because the
    /// elimination is by `rewrite`, which cannot see through the `if` inside
    /// `unless_null` on its own.
    fn block_slprop(b: &Block) -> String {
        // A block handed over by a call is already typed: the guard encloses
        // the callee's own words, not raw bytes, and restating it as bytes
        // would name a slprop nobody has.
        if let Some(t) = &b.taken {
            return t.clone();
        }
        let n = match &b.array {
            Some(a) => a.nbytes.clone(),
            None => format!("{}_sizeof", b.pn),
        };
        format!(
            "(mem_pts_to {t} 1.0R ({f} (SizeT.v {n})) ** freeable {t} {n})",
            t = b.tmp,
            f = b.fill,
            n = n
        )
    }

    /// Start tracking a block a call just handed over. The pointer is an
    /// ordinary value and goes into the local's slot like any other; what is
    /// new is that the caller now holds the block's points-to and its
    /// `freeable`, and nothing but this record would say so. The block arrives
    /// initialised -- the `ensures` names the value it holds -- and, unless the
    /// return type is `_nullable`, already past its nullness test, which is the
    /// difference between taking one over and allocating one.
    fn take_block(&mut self, var: &Ident, init: &Expr, v: &str) -> Result<(), String> {
        let Some(rb) = self.allocating_call(init) else {
            return Ok(());
        };
        if self.in_branch {
            return Err("a call returning a block inside a branch".to_string());
        }
        self.blocks.retain(|b| b.var != *var.val);
        self.blocks.push(Block {
            var: var.val.to_string(),
            tmp: v.to_string(),
            pn: rb.pn,
            fill: "uninit",
            // A `_nullable` return may have failed, and the block is behind
            // the same guard an allocation's is until the source tests it.
            checked: rb.guarded.is_none(),
            init: true,
            freed: false,
            scattered: BTreeSet::new(),
            zero: None,
            taken: rb.guarded.map(|g| g.replace(PTR_HOLE, v)),
            array: None,
        });
        Ok(())
    }

    /// A call whose result is a block the callee allocated, with the Palow name
    /// of what it points at. The `_allocated` on the callee's return type is
    /// the whole of C's vocabulary for this, and the caller reads it the same
    /// way the callee's `ensures` wrote it.
    fn allocating_call(&self, e: &Expr) -> Option<RetBlock> {
        match &strip_vattr(e).val {
            ExprT::Cast(inner, _) => self.allocating_call(inner),
            ExprT::FnCall(name, _) => self
                .callees
                .get(&*name.val.to_string())
                .and_then(|c| c.allocated.clone()),
            _ => None,
        }
    }

    /// An allocation of a single object, with the Palow name of the type
    /// allocated. `malloc(sizeof(T) * n)` is an array allocation and is not
    /// this; nor is a flexible-array-member allocation.
    fn alloc_of(&self, e: &Expr) -> Option<(&'static str, String, Option<(String, Vec<String>)>)> {
        let e = strip_vattr(e);
        let e = match &e.val {
            ExprT::Cast(inner, _) => strip_vattr(inner),
            _ => e,
        };
        match &e.val {
            ExprT::Malloc(ty) => palow_name(self.tds, ty).map(|pn| ("malloc", pn, None)),
            // `calloc` of a *scalar* hands back a readable object: the storage
            // is all zeros and the type says that is the encoding of zero.
            // Only a scalar, because an aggregate's claim would be a generated
            // `_claim` the struct emitter does not write.
            ExprT::Calloc(ty) => palow_name(self.tds, ty).map(|pn| {
                let scalar = matches!(
                    peel(self.tds, ty).val,
                    TypeT::Int { .. } | TypeT::SizeT | TypeT::Bool
                );
                let z = zero_value(self.tds, ty)
                    .ok()
                    .zip(zero_repr_proof(self.tds, ty))
                    .filter(|_| scalar);
                ("calloc", pn, z)
            }),
            _ => None,
        }
    }

    /// `malloc(sizeof(T) * n)`, with the element type and the count.
    fn array_alloc_of(&self, e: &Expr) -> Option<(&'static str, Rc<Type>, Rc<Expr>)> {
        let e = strip_vattr(e);
        let e = match &e.val {
            ExprT::Cast(inner, _) => strip_vattr(inner),
            _ => e,
        };
        match &e.val {
            ExprT::MallocArray(ty, n) => Some(("malloc", ty.clone(), n.clone())),
            ExprT::CallocArray(ty, n) => Some(("calloc", ty.clone(), n.clone())),
            _ => None,
        }
    }

    /// `p = malloc(sizeof(T) * n)` for a local pointer `p`.
    ///
    /// The block is the same object a single-object allocation produces -- raw
    /// bytes under a nullness guard -- but it is claimed at the array view, so
    /// the elements carry their own initialisation state and a subscript needs
    /// no help from the contract to know the length.
    fn allocate_array(
        &mut self,
        var: &Ident,
        which: &str,
        ty: &Type,
        count: &Expr,
    ) -> Result<String, String> {
        if self.in_branch {
            return Err("an allocation inside a branch".to_string());
        }
        let (Some(pn), Some(esize)) = (palow_name(self.tds, ty), palow_sizeof(self.tds, ty)) else {
            return Err(format!(
                "an array allocation of {}",
                describe(self.tds.resolve(ty))
            ));
        };
        if !has_repr(self.tds, ty) {
            return Err(format!(
                "an array allocation of {}",
                describe(self.tds.resolve(ty))
            ));
        }
        // `n * sizeof(T)` is computed in `size_t`, so it may overflow -- and C
        // gives the result no meaning when it does. The obligation is real
        // code, discharged by the function's own `_requires`, so without one
        // there is nothing to discharge it with unless the count is written
        // down, in which case the product is too.
        // A count C computed at compile time is still a count that is written
        // down -- `sizeof(struct vec) + n` is not, but `1 + 0` is, and the
        // difference between the two is whether anything in it can vary.
        fn lit(e: &Expr) -> Option<u64> {
            match &strip_vattr(e).val {
                ExprT::IntLit(k, _) => u64::try_from(&**k).ok(),
                ExprT::Cast(inner, _) => lit(inner),
                ExprT::BinOp(op, a, b) => {
                    let (a, b) = (lit(a)?, lit(b)?);
                    match op {
                        BinOp::Add => a.checked_add(b),
                        BinOp::Sub => a.checked_sub(b),
                        BinOp::Mul => a.checked_mul(b),
                        BinOp::Div if b != 0 => Some(a / b),
                        BinOp::Mod if b != 0 => Some(a % b),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        let literal = lit(count);
        let (n, nbytes) = match literal {
            Some(k) => (format!("{}sz", k), format!("{}sz", esize * k)),
            None => {
                if !self.requires_ok {
                    return Err(
                        "an array allocation, whose size obligation needs a `_requires` that is \
                         not translated"
                            .to_string(),
                    );
                }
                let n = self.index(count)?;
                let nbytes = format!("({}sz `SizeT.mul` {})", esize, n);
                (n, nbytes)
            }
        };
        // `calloc` hands back storage that already holds a value, so its
        // elements arrive readable. Which value depends on what the element
        // type makes of an all-zero range, and only a type that has such a
        // value can say.
        let zero = match which {
            // A value is not enough: the type also has to say that an all-zero
            // range represents it, and not every type does.
            "calloc" => zero_value(self.tds, ty)
                .ok()
                .zip(zero_repr_proof(self.tds, ty)),
            _ => None,
        };
        let tmp = self.fresh(&var.val);
        self.lines
            .push(format!("let {} = {} {};", tmp, which, nbytes));
        self.blocks.retain(|b| b.var != *var.val);
        self.blocks.push(Block {
            var: var.val.to_string(),
            tmp: tmp.clone(),
            pn,
            fill: if which == "calloc" {
                "zeroed"
            } else {
                "uninit"
            },
            checked: false,
            init: false,
            freed: false,
            scattered: BTreeSet::new(),
            zero: None,
            taken: None,
            array: Some(ArrayBlock {
                n,
                esize: format!("{}sz", esize),
                nbytes,
                zero,
                filled: false,
            }),
        });
        Ok(tmp)
    }

    /// `p = malloc(sizeof(T))` for a local pointer `p`.
    ///
    /// The pointer itself is an ordinary value and goes into `p`'s slot like
    /// any other. What is new is the resource that comes with it, which stays
    /// under `unless_null` until the source tests the pointer.
    fn allocate(
        &mut self,
        var: &Ident,
        which: &str,
        pn: &str,
        zero: Option<(String, Vec<String>)>,
    ) -> Result<String, String> {
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
            init: zero.is_some(),
            freed: false,
            scattered: BTreeSet::new(),
            zero,
            taken: None,
            array: None,
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
            match &b.array {
                // Nothing to claim: what the guard held is the points-to
                // itself, so spending the guard is the whole step.
                _ if b.taken.is_some() => vec![format!("elim_unless_null {} {};", b.tmp, sl)],
                None => vec![
                    format!("elim_unless_null {} {};", b.tmp, sl),
                    match &b.zero {
                        Some((z, why)) => {
                            format!("{} {}_claim {} {};", why.join(" "), b.pn, b.tmp, z)
                        }
                        None => format!("{}_claim_uninit {};", b.pn, b.tmp),
                    },
                ],
                Some(a) => vec![
                    format!("elim_unless_null {} {};", b.tmp, sl),
                    match &a.zero {
                        // `calloc`'s zeros only mean a value once something
                        // says that an all-zero range *is* the encoding of
                        // zero. Nothing else in the generated code needs that,
                        // so it is named here rather than left to a pattern.
                        Some((z, why)) => format!(
                            "{} array_claim_zeroed {}_repr {} {} {} #{};",
                            why.join(" "),
                            b.pn,
                            b.tmp,
                            a.esize,
                            a.n,
                            z
                        ),
                        None => format!(
                            "array_claim_uninit {}_repr {} {} {};",
                            b.pn, b.tmp, a.esize, a.n
                        ),
                    },
                ],
            },
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
        // `free(alloc())` never names the block at all. There is no local to
        // look up, but there is nothing to look up either: the call's result
        // is the block, and the three statements that give it back can be
        // written against the temporary the call was bound to.
        if let Some(rb) = self.allocating_call(arg)
            && rb.guarded.is_none()
        {
            let tmp = self.rvalue(arg)?;
            self.lines.push(format!("{}_forget {};", rb.pn, tmp));
            self.lines.push(format!("{}_reveal_uninit {};", rb.pn, tmp));
            self.lines.push(format!("free {};", tmp));
            return Ok(());
        }
        let name = match &strip_vattr(arg).val {
            ExprT::Var(v) => v.val.to_string(),
            _ => return Err("a `free` of something other than a local".to_string()),
        };
        // A block the caller handed over: the `_allocated` refinement put a
        // `freeable` in the precondition and `_consumes` says it is not wanted
        // back, so this is the same three statements as below with the
        // parameter's own address in place of the block's.
        if let Some(pn) = self.freeables.get(&name) {
            let pn = pn.clone();
            if !self.consumed_freed.insert(name.clone()) {
                return Err(format!("a second `free` of `{}`", name));
            }
            self.lines.push(format!("{}_forget var_{};", pn, name));
            self.lines
                .push(format!("{}_reveal_uninit var_{};", pn, name));
            self.lines.push(format!("free var_{};", name));
            return Ok(());
        }
        let found = self
            .blocks
            .iter()
            .position(|b| b.var == name && b.checked && !b.freed);
        // No allocation here holds it -- but a contract that spliced its own
        // ownership in can be holding both the extent and the `freeable`, in
        // words the emitter does not read. It cannot say how long the extent
        // is either, which is why this goes through the step that asks the
        // ownership rather than the caller; and if the splice did not in fact
        // grant it, F* rejects the `free`.
        let Some(i) = found else {
            if self.spliced_own
                && !self.blocks.iter().any(|b| b.var == name)
                && let Ok(ty) = self.ty_of(arg)
                && let Some(pt) = pointee(self.tds, &ty)
                && let Some(pn) = palow_name(self.tds, &pt)
                && let Some(es) = palow_sizeof(self.tds, &pt)
            {
                let v = self.rvalue(arg)?;
                self.lines
                    .push(format!("array_forget_full {}_repr {} {}sz;", pn, v, es));
                self.lines.push(format!("free {};", v));
                return Ok(());
            }
            return Err(format!(
                "a `free` of `{}`, which does not hold a checked block",
                name
            ));
        };
        let (tmp, pn, init) = {
            let b = &self.blocks[i];
            (b.tmp.clone(), b.pn.clone(), b.init)
        };
        match &self.blocks[i].array.clone() {
            Some(a) if a.filled => self.lines.push(format!(
                "array_forget_full {}_repr {} {};",
                pn, tmp, a.esize
            )),
            Some(a) => self
                .lines
                .push(format!("array_forget {}_repr {} {};", pn, tmp, a.esize)),
            None => {
                if init {
                    self.lines.push(format!("{}_forget {};", pn, tmp));
                }
                self.lines.push(format!("{}_reveal_uninit {};", pn, tmp));
            }
        }
        self.lines.push(format!("free {};", tmp));
        self.blocks[i].freed = true;
        Ok(())
    }

    /// Store into an lvalue, choosing the initialising store when the target
    /// is a slot that has not been written yet.
    fn store(&mut self, lhs: &Expr, pn: &str, value: &str) -> Result<(), String> {
        if let Some(p) = self.unalias(lhs) {
            return self.store(&p, pn, value);
        }
        // Whatever was known about the code pointers here is stale now; the
        // caller re-establishes it if the store was a decay.
        self.clear_fn_notes(lhs);
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
                let a = self.slots[i].addr.clone();
                self.lines.push(format!("{}_{} {} {};", pn, op, a, value));
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
                    let f = self.focus_elem(inner, None, true)?;
                    self.lines.extend(f.open_write.iter().cloned());
                    self.lines
                        .push(format!("{} {} {};", f.write_fn, f.at, value));
                    self.lines.extend(f.close_write);
                    return Ok(());
                }
            }
        }
        if matches!(lhs.val, ExprT::Member(..) | ExprT::Index(..)) {
            let f = self.place(lhs, true)?;
            self.lines.extend(f.open_write.iter().cloned());
            match &f.bits {
                // Storing into a bit-field is a read, a substitution and a
                // write back of the whole unit, because the neighbours it
                // shares the unit with have to survive the store. C compiles
                // it to exactly this. The masking C does to the stored value
                // is `put`'s, so an out-of-range value truncates rather than
                // breaking the unit.
                Some(pos) => {
                    let u = self.fresh("unit");
                    self.lines
                        .push(format!("let {} = {}_read {};", u, f.pn, f.at));
                    self.lines
                        .push(format!("{}_write {} {};", f.pn, f.at, pos.put(&u, &value)));
                }
                None => self
                    .lines
                    .push(format!("{} {} {};", f.write_fn, f.at, value)),
            }
            self.lines.extend(f.close_write);
            return Ok(());
        }
        let a = self.addr(lhs)?;
        // A store of a whole union value picks the live member from the value
        // itself, which the emitter does not read back.
        self.active.remove(&a);
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
        &mut self,
        clause: &Exprs,
        what: &str,
        body: Option<&Stmts>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>), String> {
        let mut binders: Vec<String> = Vec::new();
        let mut owns: Vec<String> = Vec::new();
        let mut locals: HashMap<String, String> = HashMap::new();
        // A loop invariant rebinds every value it mentions, which is the point
        // for a local the body changes and a disaster for one it does not: a
        // local bound existentially and then constrained by nothing is a local
        // whose value the loop has forgotten. Pulse's frame rule already
        // carries what the body leaves alone, and carrying it *outside* the
        // invariant is the only way its value survives. So the invariant
        // covers exactly the locals the body may write and the ones a clause
        // names -- which for a nested loop is a much smaller set than
        // everything in scope, and is why an inner loop no longer destroys
        // what the outer one knows.
        let kept: Option<HashSet<String>> = body.map(|b| {
            let mut t = Touched::default();
            touch_stmts(b, &mut t);
            touch_exprs(clause, &mut t);
            t.written.union(&t.vars).cloned().collect()
        });
        // A clause that states ownership is the author speaking about storage
        // the generated frame would otherwise claim as well, and two claims to
        // one object is not a frame. So whatever such a clause names is left
        // out of the generated half and taken from the author's words instead.
        let (own_clauses, prop_clauses): (Exprs, Exprs) = clause
            .iter()
            .cloned()
            .partition(|e| is_slprop_clause(self.tds, e));
        let mut stated: HashSet<String> = HashSet::new();
        for e in own_clauses.iter() {
            spliced_names(e, &mut stated);
        }
        // An author's ownership clause binds a fresh name for what a slot
        // holds, so a function-pointer validity that was seeded at a concrete
        // address is no longer spelled that way once the clause has been
        // proved. Put it down by inference instead.
        if !own_clauses.is_empty() {
            let held: Vec<String> = self.seeded.iter().map(|s| s.3.clone()).collect();
            self.laundered.extend(held);
        }
        for s in &self.slots {
            if let Some(k) = &kept
                && !k.contains(&s.name)
            {
                continue;
            }
            if stated.contains(&s.name) {
                continue;
            }
            if !s.init {
                // The frame would have to say that the slot still holds
                // storage rather than a value, and the body would have to
                // leave it that way. C that writes a local for the first time
                // inside a loop is real, but it is not this milestone.
                return Err(format!("{} with `{}` not yet written", what, s.name));
            }
            let b = format!("inv_{}", s.name);
            binders.push(format!("({}: {})", b, s.fstar_ty));
            owns.push(s.pts_to(&b));
            locals.insert(s.name.clone(), b);
        }
        // A local that is a name for a place rather than storage of its own
        // has no binder to stand for it, and needs none: its value is the
        // address of the place, which an invariant can spell exactly as the
        // body does. Without this `struct list_node *entry = &item->link;`
        // would come out as `var_entry` in the invariant -- a name nothing
        // declares -- while the body says `var_item +! ...`.
        for (q, place) in self.aliases.clone() {
            if locals.contains_key(&q) {
                continue;
            }
            let before = self.lines.len();
            let a = self.addr(&place);
            let quiet = self.lines.len() == before;
            self.lines.truncate(before);
            if let (Ok(a), true) = (a, quiet) {
                locals.insert(q, a);
            }
        }
        let mut pointees: HashMap<String, (Option<String>, Option<String>)> = HashMap::new();
        // A global array is named in an invariant the way it is named in a
        // contract -- `g[i]`, not `g` -- so the binder standing for its
        // contents has to be reachable as a pointee rather than as a local's
        // value. The invariant is a contract about one point in the body, and
        // the two should not need different words for the same object.
        let mut olds: HashMap<String, String> = HashMap::new();
        let mut arrays: HashSet<String> = self.arrays.keys().cloned().collect();
        for s in &self.slots {
            if s.global && s.array.is_some() {
                let b = format!("inv_{}", s.name);
                pointees.insert(s.name.clone(), (Some(b.clone()), Some(b)));
                arrays.insert(s.name.clone());
            }
        }
        for o in self.owned {
            if stated.contains(&o.base) {
                continue;
            }
            let b = format!("inv_val_{}", o.base);
            binders.push(format!("({}: {})", b, o.vty));
            owns.push(format!("{}{}", o.pre, b));
            // `_old` is the function's entry state, not this iteration's, so
            // it gets the signature's ghost binder rather than the invariant's.
            pointees.insert(o.base.clone(), (Some(b.clone()), Some(b)));
            olds.insert(o.base.clone(), o.entry.clone());
        }

        let spec = Spec {
            tds: self.tds,
            env: &self.env,
            pointees,
            olds,
            arrays,
            olens: self.olens.clone(),
            // A loop invariant binds a fresh value for every struct it
            // carries, and the deep ownership of a fresh value is not
            // something the invariant has a name for yet, so a clause that
            // reaches into one is dropped with its own reason.
            owns: HashMap::new(),
            // An ownership clause in a body-level annotation is written about
            // the objects in scope there, and a local in scope there is a
            // slot: `$&(x)` has to be the slot's address, not a parameter's.
            addrs: self
                .slots
                .iter()
                .map(|s| (s.name.clone(), s.addr.clone()))
                .collect(),
            guarded: self.guarded.clone(),
            guards: RefCell::new(Vec::new()),
            ret: String::new(),
            locals,
            uses: RefCell::new(HashSet::new()),
            signed_ok: false,
            valued: RefCell::new(Vec::new()),
        };
        for e in own_clauses.iter() {
            let ExprT::InlinePulse(code, _) = &strip_vattr(e).val else {
                return Err(format!(
                    "{} with an ownership clause that is not inline Pulse",
                    what
                ));
            };
            owns.push(spec.inline_pulse(code, When::Pre)?);
        }
        let mut props: Vec<String> = Vec::new();
        for e in prop_clauses.iter() {
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
        self.uses.extend(spec.uses.borrow().iter().cloned());
        Ok((binders, owns, props))
    }

    /// The same frame, written out as one slprop.
    fn frame_slprop(&mut self, clause: &Exprs, what: &str, indent: &str) -> Result<String, String> {
        let (binders, owns, props) = self.frame(clause, what, None)?;
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
        if !requires.is_empty() {
            return Err("a loop with its own `requires`".to_string());
        }
        let breaks = has_break(body);
        if self.has_out {
            return Err("a loop in a function with an `_out` parameter".to_string());
        }

        let (binders, owns, props) = self.frame(inv, "a loop", Some(body))?;

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
        let was_loop = self.in_loop;
        self.in_loop = true;
        let was_mark = self.loop_mark.replace(self.slots.len());
        let inits: Vec<bool> = self.slots.iter().map(|s| s.init).collect();
        // A declaration inside the body is in scope for the rest of the body
        // and nowhere else, so the environment is extended as the statements
        // go by and restored at the closing brace, as it is for a branch.
        let outer_env = self.env.clone();
        let mark = self.slots.len();
        let r = (|| -> Result<(), String> {
            for s in body.iter() {
                self.env.push_stmt(s);
                self.stmt(s)?;
            }
            // Storage declared in the body belongs to the iteration, and the
            // invariant has to hold at the closing brace without it: Pulse
            // would otherwise be asked to carry a local across an edge where C
            // says its lifetime has ended.
            self.release_from(mark);
            Ok(())
        })();
        self.env = outer_env;
        self.slots.truncate(mark);
        self.in_branch = was_branch;
        self.in_loop = was_loop;
        self.loop_mark = was_mark;
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
        // Pulse's `while` carries, implicitly, that the condition is false on
        // the way out. A `break` leaves from the middle, where the condition
        // still holds, so that promise has to be given up -- `ensures true`
        // is how Pulse is told to stop making it. Nothing is lost that the
        // source promised: C makes no claim about a loop it jumped out of,
        // and what the author does claim arrives as `_ensures`, asserted
        // below. A loop without a `break` keeps the negated condition.
        if breaks {
            self.lines.push("  ensures true".to_string());
        }
        self.divergent = true;
        self.lines.push("{".to_string());
        self.lines.extend(body_lines.iter().map(|l| indent(l)));
        self.lines.push("};".to_string());
        // A loop's `_ensures` is what holds when it exits, and a `break` is
        // the reason it needs saying: the ordinary exit is covered by the
        // invariant and the negated condition, but a `break` leaves from the
        // middle, where the condition still holds.
        //
        // Pulse's `while` takes an `ensures` too, but it is a *prop* over the
        // enclosing scope, and every local a loop invariant talks about is
        // existentially bound inside the invariant, so there is no name for it
        // there. Here the same claim is an assertion after the loop instead,
        // which costs the reads it names and means exactly what the source
        // says. What holds at the exit is what holds just after it.
        for e in ensures.iter() {
            let p = self.prop(e)?;
            if p != "True" {
                self.lines.push(format!("assert (pure ({}));", p));
            }
        }
        Ok(())
    }

    /// One C statement, plus whatever the statement borrowed and has to give
    /// back. A local array handed to a callee is converted to the view the
    /// callee asks for, and the way back can only be emitted once the call
    /// has been -- so it is owed here rather than emitted in place.
    fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        let r = self.stmt_inner(s);
        let close = std::mem::take(&mut self.pending_close);
        let open = std::mem::take(&mut self.own_open);
        r?;
        self.lines.extend(close);
        self.own_open = open;
        self.close_own();
        Ok(())
    }

    fn stmt_inner(&mut self, s: &Stmt) -> Result<(), String> {
        match &s.val {
            StmtT::Decl(name, ty) => {
                if self.aliases.contains_key(&*name.val.to_string())
                    || self.is_array_alias(&name.val.to_string())
                {
                    return Ok(());
                }
                self.alloc_slot(name, ty)?;
                Ok(())
            }
            // A variable-length array. It is the same object a fixed-size
            // local array is -- `n` elements of storage, each written on its
            // own -- and the only difference is that `n` is a value rather
            // than a constant, which the model's `array_stack_alloc` already
            // takes. What C does not give is any guarantee that `n` elements
            // fit in a `size_t`, so the byte count is a real obligation and
            // the function's own `_requires` is the only thing that can
            // discharge it.
            StmtT::DeclStackArray {
                name,
                elem_type,
                size,
            } => {
                let (Some(pn), Some(esize), Some(ety)) = (
                    palow_name(self.tds, elem_type),
                    palow_sizeof(self.tds, elem_type),
                    fstar_type(self.tds, elem_type),
                ) else {
                    return Err(format!(
                        "a stack array of {}",
                        describe(self.tds.resolve(elem_type))
                    ));
                };
                if !has_repr(self.tds, elem_type) {
                    return Err(format!(
                        "a stack array of {}",
                        describe(self.tds.resolve(elem_type))
                    ));
                }
                if !self.requires_ok {
                    return Err(
                        "a stack array, whose size obligation needs a `_requires` that is not \
                         translated"
                            .to_string(),
                    );
                }
                let n = self.index(size)?;
                self.lines.push(format!(
                    "let loc_{} = array_stack_alloc {}_repr {}sz {} ({}sz `SizeT.mul` {});",
                    name.val, pn, esize, n, esize, n
                ));
                self.slots.push(Slot {
                    name: name.val.to_string(),
                    addr: format!("loc_{}", name.val),
                    palow_ty: pn,
                    fstar_ty: format!(
                        "(s: Seq.seq (option {}) {{ Seq.length s == SizeT.v {} }})",
                        ety, n
                    ),
                    init: true,
                    array: Some((format!("{}sz", esize), true)),
                    global: false,
                    union_arm: None,
                    filling: None,
                    holds_fn: BTreeMap::new(),
                    scattered: BTreeSet::new(),
                });
                Ok(())
            }
            StmtT::Let(name, ty, init) => {
                let v = match (self.alloc_of(init), self.array_alloc_of(init)) {
                    (Some((which, pointee, z)), _) => self.allocate(name, which, &pointee, z)?,
                    (_, Some((which, ty, n))) => self.allocate_array(name, which, &ty, &n)?,
                    _ => {
                        let v = self.rvalue(init)?;
                        self.take_block(name, init, &v)?;
                        v
                    }
                };
                let pn = self.alloc_slot(name, ty)?;
                self.lines
                    .push(format!("{}_write_uninit loc_{} {};", pn, name.val, v));
                let held = self.fn_notes(init);
                let slot = self.slots.last_mut().unwrap();
                slot.init = true;
                slot.holds_fn = held;
                Ok(())
            }
            StmtT::Assign(lhs, rhs) => {
                // The alias itself: nothing is stored, because the pointer is
                // a name and not an object.
                if let Some(v) = lvalue_name(lhs) {
                    if self.aliases.contains_key(&v) || self.is_array_alias(&v) {
                        return Ok(());
                    }
                }
                let ty = self.ty_of(lhs)?;
                // An array is not assignable in C; this is the initialiser of
                // a local array, which clang has already padded out to the
                // declared length. It means one store per element, and saying
                // so is the whole translation: each store then goes through
                // the same element focus a subscript assignment uses, and the
                // sequence the slot holds records what has been written.
                if let TypeT::FixedArray(_, n) = &self.tds.resolve(&ty).val {
                    if let ExprT::ArrayInit { elems, .. } = &strip_vattr(rhs).val {
                        if elems.len() as u64 != *n {
                            return Err("an array initialiser of another length".to_string());
                        }
                        let elems = elems.clone();
                        for (i, e) in elems.iter().enumerate() {
                            let idx = ExprT::IntLit(
                                Rc::new(BigInt::from(i)),
                                TypeT::SizeT.with_loc(s.loc.clone()),
                            )
                            .with_loc(s.loc.clone());
                            let at = ExprT::Index(Rc::new(lhs.as_ref().clone()), idx)
                                .with_loc(s.loc.clone());
                            let st = StmtT::Assign(at, e.clone()).with_loc(s.loc.clone());
                            self.stmt(&st)?;
                        }
                        return Ok(());
                    }
                }
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("an assignment to {}", describe(&ty)))?;
                if let ExprT::Var(v) = &strip_vattr(lhs).val {
                    if let Some((which, pointee, z)) = self.alloc_of(rhs) {
                        let value = self.allocate(v, which, &pointee, z)?;
                        return self.store(lhs, &pn, &value);
                    }
                    if let Some((which, ty, n)) = self.array_alloc_of(rhs) {
                        let value = self.allocate_array(v, which, &ty, &n)?;
                        return self.store(lhs, &pn, &value);
                    }
                }
                let v = self.rvalue(rhs)?;
                if let ExprT::Var(n) = &strip_vattr(lhs).val {
                    self.take_block(n, rhs, &v)?;
                }
                self.store(lhs, &pn, &v)?;
                self.note_fn_store(lhs, rhs);
                self.note_union_store(lhs, rhs);
                Ok(())
            }
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => {
                // The body runs an unknown number of times, so what was live
                // before it says nothing about what is live after.
                self.active.clear();
                self.loop_(cond, inv, requires, ensures, body)?;
                self.active.clear();
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
                // As with an `if`: the arms need not agree on which union
                // member they leave live, so none is known afterwards.
                self.active.clear();

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
                // As for an `if`: a slot only still holds a known function
                // after the join if every case left the same one in it.
                let holds = last.holds.clone();
                for (i, slot) in self.slots.iter_mut().enumerate() {
                    if arms.iter().any(|(_, a)| a.holds.get(i) != holds.get(i)) {
                        slot.holds_fn.clear();
                    }
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
            // `_assert` of a hand-written slprop is an ownership assertion,
            // not a proposition, so it is checked as written rather than
            // wrapped in `pure`.
            StmtT::Assert(e)
                if matches!(&strip_vattr(e).val,
                    ExprT::InlinePulse(_, t) if matches!(self.tds.resolve(t).val, TypeT::SLProp)) =>
            {
                if !self.tds.splice_inline {
                    return Err(self.tds.no_splice());
                }
                let ExprT::InlinePulse(code, _) = &strip_vattr(e).val else {
                    unreachable!()
                };
                let t = flatten_fragment(&self.inline_pulse(code)?)?;
                self.lines.push(format!("assert ({});", t));
                Ok(())
            }
            StmtT::Assert(e) => {
                let p = self.prop(e)?;
                self.lines.push(format!("assert (pure ({}));", p));
                Ok(())
            }
            // See `ghost_replaced`.
            // Pulse has `break` and `continue`, and they mean what C means.
            // What they do not have is a way to leave a *slot* behind: a local
            // allocated inside the loop body would have to be released on the
            // way out, and neither statement runs the releases between it and
            // the end of the body. Releasing them here is easy enough; what is
            // not is what a `break` does to the *exit condition*. Pulse's
            // `while` promises the condition is false on the way out, a loop
            // with a `break` has to give that promise up, and the invariant --
            // which is all that is left -- binds every local existentially. So
            // a loop that breaks past a local is one whose `_ensures` about
            // that local would rest on nothing.
            StmtT::Break | StmtT::Continue if self.loop_mark != Some(self.slots.len()) => Err(
                format!("{} past a local allocated in the loop", stmt_kind(s)),
            ),
            StmtT::Break | StmtT::Continue if !self.in_loop => {
                Err(format!("{} outside a loop", stmt_kind(s)))
            }
            StmtT::Break => {
                self.lines.push("break;".to_string());
                Ok(())
            }
            StmtT::Continue => {
                self.lines.push("continue;".to_string());
                Ok(())
            }
            StmtT::GhostStmt(code) if aux_activate(code).is_some() => {
                let (ty, arm, obj) = aux_activate(code).unwrap();
                self.activate_arm(ty, arm, obj)
            }
            StmtT::GhostStmt(code) if matches!(aux_fn_kind(code), Some(AuxFnKind::Fold)) => {
                // The end of the bracket `$unfold-uninit` opened: the fields
                // have all been written and gathered, so the element is a
                // value again and goes back into the array.
                self.close_open_elem(code);
                Ok(())
            }
            StmtT::GhostStmt(code) if ghost_replaced(code) => {
                // `$unfold-uninit` is the one member of the pair that says
                // something Palow cannot see for itself: that the object is
                // storage the function owns but whose contents are not yet
                // valid. Palow spells that as an uninitialised slot -- the
                // field writes scatter into it and the last one gathers it
                // back up -- so the statement turns into a note rather than
                // into code.
                if let Some(e) = uninit_open_arg(code) {
                    self.note_uninit(e);
                }
                Ok(())
            }
            StmtT::GhostStmt(_) if !self.tds.splice_inline => Err(self.tds.no_splice()),
            StmtT::GhostStmt(code) => {
                let t = self.inline_pulse(code)?;
                self.lines.push(format!("{};", t.trim()));
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
                // An indirect call in statement position still produces a
                // value; binding it and dropping it is what C does.  So does
                // an increment, and there discarding the value is the usual
                // case rather than the odd one.
                ExprT::FnPtrCall(..)
                | ExprT::PreIncr(..)
                | ExprT::PostIncr(..)
                | ExprT::PreDecr(..)
                | ExprT::PostDecr(..) => self.rvalue(e).map(|_| ()),
                // Zeroing a whole object is a write of the type's zero value.
                // That is weaker than what `memset` really does, because it
                // says nothing about the padding, and weaker is the safe
                // direction: the padding stays owned and unspecified either
                // way, which is exactly what `struct_S_padding` already says.
                // Filling an array with zeros. What Palow has to say here it
                // already had to say for `calloc`: an all-zero byte range is
                // the encoding of 0 for the element type, which is
                // `encode_zero`, and the rest is the machine layer making the
                // range all-zero.
                //
                // Only a fill of zero is covered, which is the fill C code
                // reliably means -- `memset` with any other value is well
                // defined only for byte-sized types.
                ExprT::Memset(ty, p, value, count) => {
                    if !is_zero(value) {
                        return Err("a `memset` with a fill other than zero".to_string());
                    }
                    let Some(esize) = palow_sizeof(self.tds, ty) else {
                        return Err(format!("a `memset` of {}", describe(self.tds.resolve(ty))));
                    };
                    let ArrayPlace {
                        addr: arr,
                        pn,
                        close_write: close,
                        maybe,
                        ..
                    } = self.array_place(p)?;
                    let z = zero_value(self.tds, ty)?;
                    // `Seq.length xs == n` is what says the fill stays inside
                    // the array, and for a parameter that can only come from
                    // the function's own `_requires`.
                    if !self.array_len_known(p) && !self.requires_ok {
                        return Err(
                            "a `memset`, whose length obligation needs a `_requires` that is not \
                             translated"
                                .to_string(),
                        );
                    }
                    let (n, nbytes) = match int_lit(count) {
                        Some(k) => (format!("{}sz", k), format!("{}sz", esize * k)),
                        None => {
                            let n = self.index(count)?;
                            (n.clone(), format!("({}sz `SizeT.mul` {})", esize, n))
                        }
                    };
                    let repr = if maybe {
                        format!("(maybe_repr {}_repr {})", pn, esize)
                    } else {
                        format!("{}_repr", pn)
                    };
                    let z = if maybe { format!("(Some {})", z) } else { z };
                    self.lines.push(format!("encode_zero {};", esize));
                    self.lines.push(format!(
                        "array_memset_zero {} {} {}sz {} {} {};",
                        repr, arr, esize, n, nbytes, z
                    ));
                    self.lines.extend(close);
                    Ok(())
                }
                ExprT::MemsetZero(ty, p) => {
                    // A structure is written whole, which needs the generated
                    // storage operations; a struct with an array field has
                    // none, because filling the array is the other half of
                    // `memset` and is not translated yet.
                    if matches!(
                        &peel(self.tds, ty).val,
                        TypeT::TypeRef(TypeRefKind::Struct(..))
                    ) && !storable_struct(self.tds, ty)
                    {
                        return Err(format!("a `memset` of {}", describe(ty)));
                    }
                    let z = zero_value(self.tds, ty)?;
                    let pn = palow_name(self.tds, ty)
                        .ok_or_else(|| format!("a `memset` of {}", describe(ty)))?;
                    let place = deref_of(p);
                    self.store(&place, &pn, &z)
                }
                _ => Err(format!(
                    "a call in statement position that is not one: {}",
                    expr_kind(e)
                )),
            },
            StmtT::If {
                cond,
                then_branch,
                else_branch,
                ensures,
            } => {
                // Either arm may make a different member live, and the two
                // arms need not agree, so nothing survives the join.
                self.active.clear();
                // A `_ensures` that says only what is live needs no
                // translation: Pulse computes the join of an `if` itself, so
                // the annotation exists to be checked and not to make the code
                // typecheck. One that states *ownership* is different. The two
                // arms may have established it in different words -- a
                // function pointer weakened from two different callees is the
                // case that matters -- and then only the author's own words
                // name the shape they have in common.
                let states_own = ensures.iter().any(|e| is_slprop_clause(self.tds, e));
                let mut fps: Vec<(String, String)> = Vec::new();
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
                // Pulse joins an `if` by matching on the condition, and it can
                // only reduce that match inside an arm if the condition is a
                // name. A call is not: two `if`s on the same call nest into a
                // join whose arms differ, and the outer one is then
                // unprovable. Binding the call first costs nothing -- C
                // evaluates the condition once anyway -- and makes the
                // branch hypothesis usable.
                let c = if nt.is_none() && matches!(strip_vattr(cond).val, ExprT::FnCall(..)) {
                    let t = self.fresh("cond");
                    self.lines.push(format!("let {} = {};", t, c));
                    t
                } else {
                    c
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
                // Which function a slot holds is only known after the join if
                // both arms left the same one in it. Without this, a pointer
                // assigned different functions in the two arms would be called
                // as whichever arm was translated last.
                for (i, slot) in self.slots.iter_mut().enumerate() {
                    if then.holds.get(i) != els.holds.get(i) {
                        slot.holds_fn.clear();
                    }
                }

                let (then_pre, else_pre) = match nt {
                    Some((i, null_when_true)) => {
                        let (n, l) = self.null_test_arms(i);
                        if null_when_true { (n, l) } else { (l, n) }
                    }
                    None => (Vec::new(), Vec::new()),
                };
                self.lines.push(format!("if ({})", c));
                if states_own {
                    // Pulse does not frame an `if`'s annotation, so it has to
                    // be the whole state at the join: the author's ownership
                    // plus everything they did not speak for.
                    let join = self.frame_slprop(ensures, "an `if`", "    ")?;
                    self.lines.push(format!("  ensures {}", join));
                    // Validity is not carried by any points-to -- the bytes of
                    // a code pointer say where the code is, not what it does --
                    // so a clause that speaks for a function-pointer local is
                    // the only thing that can make a call through it possible.
                    let mut stated: HashSet<String> = HashSet::new();
                    for e in ensures.iter() {
                        spliced_names(e, &mut stated);
                    }
                    for n in stated {
                        if let Some(sl) = self.slots.iter().find(|s| s.name == n) {
                            let addr = sl.addr.clone();
                            self.local_valid_fps.insert(n.clone());
                            // Nobody owns this validity once the function is
                            // over, so it is recorded as held and put down
                            // with the rest. It is laundered from the start:
                            // the author's clause bound a fresh name for what
                            // the slot holds, and that name is all there is.
                            let key = format!("$if${}", addr);
                            fps.push((addr, key.clone()));
                            self.laundered.insert(key);
                        }
                    }
                }
                self.lines.push("{".to_string());
                self.lines.extend(then_pre.iter().map(|l| indent(l)));
                self.lines.extend(then.lines.iter().map(|l| indent(l)));
                self.lines.push("} else {".to_string());
                self.lines.extend(else_pre.iter().map(|l| indent(l)));
                self.lines.extend(els.lines.iter().map(|l| indent(l)));
                self.lines.push("};".to_string());
                for (addr, key) in fps {
                    self.seeded
                        .push((addr, "_".to_string(), "_".to_string(), key));
                }
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
    ///
    /// A Pulse block's value is its last expression, so the value is appended
    /// here rather than handed back; what comes back is only whether there is
    /// one. That is what lets a returning `if` be a value in its own right,
    /// which is what a chain of early returns needs.
    fn rest(&mut self, stmts: &[Rc<Stmt>]) -> Result<bool, String> {
        for (i, s) in stmts.iter().enumerate() {
            match &s.val {
                StmtT::Return(e) => {
                    let mut v = match e {
                        Some(e) => Some(self.rvalue(e)?),
                        None => None,
                    };
                    // A `return` is not routed through `stmt`, so anything the
                    // returned expression borrowed or unfolded has to be given
                    // back here -- before the frame is released, since the
                    // frame is stated in terms of what was borrowed from.
                    let close = std::mem::take(&mut self.pending_close);
                    self.lines.extend(close);
                    self.close_own();
                    // Ghost statements after a `return` are the only way to
                    // establish a postcondition that talks about the returned
                    // value, so the value is given a name and they are run
                    // against it before the frame is released.
                    // Only the run of ghost statements directly after the
                    // `return`: anything past it is unreachable code, which is
                    // dropped here as it always has been.
                    let after: Vec<Rc<Stmt>> = stmts[i + 1..]
                        .iter()
                        .take_while(|s| matches!(s.val, StmtT::GhostStmt(_)))
                        .cloned()
                        .collect();
                    if !after.is_empty() {
                        if let Some(val) = &v {
                            let name = format!("ret_val{}", self.tmp);
                            self.tmp += 1;
                            self.lines.push(format!("let {} = {};", name, val));
                            v = Some(name.clone());
                            self.ret_binding = Some(name);
                        }
                        let r = (|| -> Result<(), String> {
                            for s in &after {
                                self.env.push_stmt(s);
                                self.stmt(s)?;
                            }
                            Ok(())
                        })();
                        self.ret_binding = None;
                        r?;
                    }
                    self.release_from(0);
                    let has = v.is_some();
                    if let Some(v) = v {
                        self.lines.push(v);
                    }
                    return Ok(has);
                }
                StmtT::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                } if returns(then_branch) || returns(else_branch) => {
                    self.active.clear();
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
                    if then_val != else_val {
                        return Err("an `if` where only one arm returns a value".to_string());
                    }
                    self.lines.push(format!("if ({})", c));
                    self.lines.push("{".to_string());
                    self.lines.extend(then_lines.iter().map(|l| indent(l)));
                    self.lines.push("} else {".to_string());
                    self.lines.extend(else_lines.iter().map(|l| indent(l)));
                    self.lines.push("}".to_string());
                    return Ok(then_val);
                }
                // A labelled block carries its own label: the statements that
                // follow the block are what a `goto` jumps *to*, so they are
                // recorded as that label's continuation and the block is
                // translated with a jump to it appended -- falling off the end
                // of a labelled block reaches the label exactly as a `goto`
                // does.
                StmtT::GotoBlock {
                    body,
                    label,
                    ensures,
                } => {
                    let cont: Vec<Rc<Stmt>> = stmts[i + 1..].to_vec();
                    self.gotos
                        .push((label.val.to_string(), cont, ensures.clone()));
                    let mut seq = body.to_vec();
                    seq.push(StmtT::Goto(label.clone()).with_loc(s.loc.clone()));
                    let r = self.rest(&seq);
                    self.gotos.pop();
                    return r;
                }
                StmtT::Goto(label) => {
                    let Some(at) = self
                        .gotos
                        .iter()
                        .rposition(|(n, _, _)| *n == label.val.to_string())
                    else {
                        return Err(format!(
                            "a `goto {}`, whose label is not in scope",
                            label.val
                        ));
                    };
                    let (_, cont, ensures) = self.gotos[at].clone();
                    // A label's `_ensures` is what the old translator needs to
                    // join the paths that reach it. Here there is no join --
                    // each path carries the continuation with it -- so what is
                    // left to do is check it, which is what the author asked
                    // for. `_live` says the storage exists, and the slots say
                    // that already.
                    for e in ensures.iter() {
                        if live_only(e) {
                            continue;
                        }
                        let p = self.prop(e)?;
                        self.lines.push(format!("assert (pure ({}));", p));
                    }
                    // Labels inside the one being jumped to are out of scope
                    // at its continuation, and so is the label itself: a
                    // `goto` backwards would be a loop, which this is not.
                    let inner = self.gotos[..at].to_vec();
                    let outer = std::mem::replace(&mut self.gotos, inner);
                    let r = self.rest(&cont);
                    self.gotos = outer;
                    return r;
                }
                _ => {
                    self.env.push_stmt(s);
                    self.stmt(s)?;
                }
            }
        }
        self.release_from(0);
        Ok(false)
    }

    /// One arm of a returning `if`, translated into its own line buffer
    /// against a copy of the state at the `if`.
    fn tail_arm(&mut self, stmts: &[Rc<Stmt>]) -> Result<(Vec<String>, bool), String> {
        let outer_env = self.env.clone();
        let outer_lines = std::mem::take(&mut self.lines);
        let outer_out = self.out_params.clone();
        let outer_slots = self.slots.clone();
        let outer_seeded = self.seeded.clone();
        let outer_open = self.open_elems.clone();
        let outer_in_branch = std::mem::replace(&mut self.in_branch, true);

        let out = self
            .rest(stmts)
            .map(|v| (std::mem::take(&mut self.lines), v));

        self.in_branch = outer_in_branch;
        self.open_elems = outer_open;
        self.seeded = outer_seeded;
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
        // What the enclosing slots hold before the arm runs. An arm is one
        // path, so what it stores is only true on that path: the other arm has
        // to start where this one did, and what survives the join is what both
        // arms agree on.
        let outer_state: Vec<(bool, BTreeMap<String, String>, BTreeSet<String>)> = self
            .slots
            .iter()
            .map(|s| (s.init, s.holds_fn.clone(), s.scattered.clone()))
            .collect();
        let outer_env = self.env.clone();
        let outer_lines = std::mem::take(&mut self.lines);
        let outer_out = self.out_params.clone();
        let outer_seeded = self.seeded.clone();
        let outer_open = self.open_elems.clone();
        let outer_in_branch = std::mem::replace(&mut self.in_branch, true);

        let result = (|| -> Result<bool, String> {
            for s in stmts.iter() {
                if let StmtT::Return(e) = &s.val {
                    // A Pulse block is an expression: leaving early means
                    // being the tail of what encloses you, which `rest`
                    // arranges by folding the statements after an `if` into
                    // the arm that falls through. A loop body has no tail to
                    // be -- but Pulse has a `return` of its own, and this is
                    // the one place worth spending it. Everything the frame
                    // holds is given back first, because nothing after this
                    // runs; whether what is left implies the postcondition is
                    // the loop invariant's business, which is where it
                    // belongs.
                    if !self.in_loop {
                        return Err("a `return` that is not in tail position".to_string());
                    }
                    let v = match e {
                        Some(e) => Some(self.rvalue(e)?),
                        None => None,
                    };
                    let close = std::mem::take(&mut self.pending_close);
                    self.lines.extend(close);
                    self.close_own();
                    self.release_from(0);
                    self.lines.push(match v {
                        Some(v) => format!("return {};", v),
                        None => "return ();".to_string(),
                    });
                    // Anything after it in this arm is unreachable, and so is
                    // the arm's own release: the frame is already gone.
                    return Ok(true);
                }
                self.env.push_stmt(s);
                self.stmt(s)?;
            }
            Ok(false)
        })();

        self.in_branch = outer_in_branch;
        let out = (|| {
            if !result? {
                self.release_from(mark);
            }
            self.seeded = outer_seeded;
            Ok(BranchResult {
                lines: std::mem::take(&mut self.lines),
                inits: self.slots[..mark].iter().map(|s| s.init).collect(),
                holds: self.slots[..mark]
                    .iter()
                    .map(|s| s.holds_fn.clone())
                    .collect(),
                out_params: std::mem::take(&mut self.out_params),
            })
        })();

        self.open_elems = outer_open;
        self.slots.truncate(mark);
        for (slot, (init, holds, scattered)) in self.slots.iter_mut().zip(outer_state) {
            slot.init = init;
            slot.holds_fn = holds;
            slot.scattered = scattered;
        }
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

    /// Put down every validity seeded since `mark`. `is_valid` is a `pure`
    /// fact, but it is `pure` behind a definition, so Pulse will not absorb it
    /// on its own.
    fn drop_seeded(&mut self, mark: usize) {
        for (addr, pre, post, g) in self.seeded.split_off(mark) {
            self.lines.push(if self.laundered.contains(&g) {
                "drop_is_valid _ _ _;".to_string()
            } else {
                format!("drop_is_valid {} {} {};", addr, pre, post)
            });
        }
    }

    /// The written fields of a scattered slot, with the Palow name of each.
    fn scattered_field_names(&self, i: usize) -> Vec<(String, String)> {
        let sn = self.slots[i].palow_ty.strip_prefix("struct_").unwrap_or("");
        let Some(si) = self.tds.structs.get(sn) else {
            return Vec::new();
        };
        si.fields
            .iter()
            .filter(|f| self.slots[i].scattered.contains(&f.name))
            .filter_map(|f| match &f.shape {
                FieldShape::One { pn } => Some((f.name.clone(), pn.clone())),
                FieldShape::Array { .. } | FieldShape::Flex { .. } => None,
            })
            .collect()
    }

    fn release_from(&mut self, mark: usize) {
        // Leaving the function: anything still held has to go, including a
        // validity seeded for a use that did not consume it -- storing a
        // decayed function in a slot, say.
        if mark == 0 && !self.ret_spliced {
            for (addr, pre, post, g) in self.seeded.clone() {
                // ...unless the contract promised it to the caller, which is
                // what a field-level `_refine` on a returned block does.
                if self.post_valid.contains(&g) {
                    continue;
                }
                self.lines.push(if self.laundered.contains(&g) {
                    "drop_is_valid _ _ _;".to_string()
                } else {
                    format!("drop_is_valid {} {} {};", addr, pre, post)
                });
            }
        }
        // An `_out` array was handed over as storage and has to leave as a
        // value: that is what the mode promises the caller. The step is pure
        // bookkeeping, but its obligation is not -- `array_somes` asks that
        // every cell was written, which is the honest reading of C's rule
        // against handing back an object that is partly indeterminate.
        if mark == 0 {
            for base in self.olens.keys().cloned().collect::<Vec<_>>() {
                // Still an `_out` parameter means nothing else has taken it
                // over; one handed on to a callee comes back already filled.
                if !self.out_params.contains(&base) {
                    continue;
                }
                let Some(a) = self.arrays.get(&base) else {
                    continue;
                };
                self.lines
                    .push(format!("array_somes {}_repr {} {};", a.pn, a.addr, a.esize));
            }
        }
        for i in (mark..self.slots.len()).rev() {
            let (addr, pn, init, array, global, scattered) = {
                let s = &self.slots[i];
                (
                    s.addr.clone(),
                    s.palow_ty.clone(),
                    s.init,
                    s.array.clone(),
                    s.global,
                    s.scattered.clone(),
                )
            };
            // A global's storage outlives the function; the contract hands it
            // straight back rather than releasing it.
            if global {
                continue;
            }
            // An array's storage view already covers whatever its elements
            // hold, so there is nothing to forget first.
            if let Some((esize, _)) = array {
                self.lines
                    .push(format!("array_stack_free {}_repr {} {};", pn, addr, esize));
                continue;
            }
            // A half-built object never became a value, so there is nothing
            // to forget as a whole: each field that did get written gives its
            // own value up, and what is left is the storage the slot started
            // with.
            if !scattered.is_empty() {
                let fpn = self.scattered_field_names(i);
                for (name, p) in fpn {
                    self.lines.push(format!(
                        "{}_forget ({} +! {}_offsetof_{});",
                        p, addr, pn, name
                    ));
                }
                self.lines.push(format!("{}_gather_uninit {};", pn, addr));
            } else if init {
                self.lines.push(format!("{}_forget {};", pn, addr));
            }
            self.lines.push(format!("{}_stack_free {};", pn, addr));
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
/// On the LP64 target Palow fixes, `ptrdiff_t` *is* `int64_t`: it shares that
/// type's storage, so it shares its conversions too.
fn convert(from: &Type, to: &Type, v: &str) -> Result<String, String> {
    let lp64 = |t: &Type| match &t.val {
        TypeT::PtrdiffT => Ast {
            val: TypeT::Int {
                signed: true,
                width: 64,
            },
            loc: t.loc.clone(),
        },
        _ => t.clone(),
    };
    convert_scalar(&lp64(from), &lp64(to), v)
}

fn convert_scalar(from: &Type, to: &Type, v: &str) -> Result<String, String> {
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
        // An array decays to a pointer to its first element. Palow already
        // names an array by that address, so the conversion is the identity.
        // What really differs between the two is the ownership, and ownership
        // is not part of the value: it is settled where the pointer is used,
        // not here.
        (TypeT::FixedArray(..), TypeT::Pointer(..)) => Ok(v.to_string()),
        // Widening a `float` to a `double` is exact and narrowing rounds, so
        // the two directions are separate functions and only the exact one is
        // invertible. Routing either through an integer -- which is what a
        // model without them has to do -- would not be the conversion C
        // performs.
        (TypeT::Float { width: 32 }, TypeT::Float { width: 64 }) => {
            Ok(format!("(float64_of_float32 {})", v))
        }
        (TypeT::Float { width: 64 }, TypeT::Float { width: 32 }) => {
            Ok(format!("(float32_of_float64 {})", v))
        }
        (TypeT::Float { width: a }, TypeT::Float { width: b }) if a == b => Ok(v.to_string()),
        // An integer converts to the nearest representable value, and every
        // integer C has fits in an `int64_t`, which is what `of_int` takes.
        (
            TypeT::Int { signed, width },
            TypeT::Float {
                width: w @ (32 | 64),
            },
        ) => {
            let widen = if *width == 64 && *signed {
                v.to_string()
            } else if *signed {
                format!("(FStar.Int.Cast.int{}_to_int64 {})", width, v)
            } else {
                format!("(FStar.Int.Cast.uint{}_to_int64 {})", width, v)
            };
            Ok(format!("(Float{}.of_int {})", w, widen))
        }
        // A float is true when it is unequal to zero, which is C's rule and
        // also `ieee_eq`'s: a NaN is not equal to zero, and so is true.
        (
            TypeT::Float {
                width: w @ (32 | 64),
            },
            TypeT::Bool,
        ) => Ok(format!("(not (Float{}.ieee_eq {} Float{}.zero))", w, v, w)),
        (
            TypeT::Bool,
            TypeT::Float {
                width: w @ (32 | 64),
            },
        ) => Ok(format!(
            "(if {} then Float{}.one else Float{}.zero)",
            v, w, w
        )),
        _ => Err(format!(
            "a conversion from {} to {}",
            describe(from),
            describe(to)
        )),
    }
}

/// The F* module a float of this width is spelled in, if Palow has one.
fn float_mod(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &peel(tds, ty).val {
        TypeT::Float {
            width: w @ (32 | 64),
        } => Some(format!("Float{}", w)),
        _ => None,
    }
}

/// A C floating-point literal. F* takes one as a string and replaces it with
/// the corresponding C constant at extraction, so the only work here is to
/// drop C's width suffix -- which is already in the type, and which F* would
/// not recognise.
fn float_literal(tds: &Typedefs, text: &str, ty: &Type) -> Result<String, String> {
    let m = float_mod(tds, ty).ok_or_else(|| format!("a literal of {}", describe(ty)))?;
    let digits = text.trim_end_matches(['f', 'F', 'l', 'L']);
    if digits.is_empty() || digits.contains('"') {
        return Err("a float literal that is not a plain constant".to_string());
    }
    Ok(format!("({}.of_literal \"{}\")", m, digits))
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

/// The all-zero value of a C type, as an F\* term. This is what `memset(p, 0,
/// sizeof(T))` leaves behind, and it exists as a separate function from the
/// initialiser machinery because there is no expression to translate.
///
/// A pointer is deliberately absent: an all-zero pointer is the null pointer
/// only on a target that says so, and Palow does not have that assumption in
/// the byte layer. A union is absent for a better reason -- zeroing it is a
/// statement about bytes, and the value it names afterwards depends on which
/// member is read.
/// The value a static object with no initialiser starts at.
///
/// This is *not* `memset` to zero. C11 6.7.9p10 says an arithmetic member
/// starts at zero and a pointer member starts at a null pointer -- a statement
/// about values, not about bytes -- so unlike `zero_value` it has an answer
/// for a pointer, and that answer is `null` on every target.
fn static_zero(tds: &Typedefs, ty: &Type) -> Result<String, String> {
    let t = peel(tds, ty);
    if matches!(&t.val, TypeT::Pointer(..) | TypeT::FnPtr { .. }) {
        return Ok("null".to_string());
    }
    if let TypeT::TypeRef(TypeRefKind::Struct(name)) = &t.val {
        let Some(si) = tds.structs.get(&*name.val) else {
            return Err(format!("a zeroed struct {}", name.val));
        };
        let mut vals = Vec::new();
        for f in &si.fields {
            let FieldShape::One { .. } = &f.shape else {
                return zero_value(tds, ty);
            };
            vals.push(format!("fld_{} = {}", f.name, static_zero(tds, &f.ty)?));
        }
        return Ok(format!("({{ {} }})", vals.join("; ")));
    }
    zero_value(tds, ty)
}

/// The lemma calls that prove a type's zero value is what an all-zero byte
/// range represents, or `None` when the type has no such value.
///
/// `calloc` is what needs this: the storage arrives all-zero, and turning
/// that into a *value* takes a fact about the type. For a scalar the fact is
/// `encode_zero`; for a struct it is the struct's own `_repr_zero`, which is
/// emitted exactly when this returns `Some` for every field. A pointer field
/// is not zeroable -- C says `calloc` gives a null pointer, but null's
/// representation is not fixed to be all-zero, and the model does not pretend
/// otherwise.
fn zero_repr_proof(tds: &Typedefs, ty: &Type) -> Option<Vec<String>> {
    let t = peel(tds, ty);
    match &t.val {
        TypeT::Int { .. } | TypeT::SizeT => {
            Some(vec![format!("encode_zero {};", palow_sizeof(tds, ty)?)])
        }
        TypeT::TypeRef(TypeRefKind::Struct(name)) => {
            let si = tds.structs.get(&*name.val)?;
            let pn = palow_name(tds, ty)?;
            if !si
                .fields
                .iter()
                .all(|f| zero_repr_proof(tds, &f.ty).is_some())
            {
                return None;
            }
            Some(vec![format!("{}_repr_zero ();", pn)])
        }
        _ => None,
    }
}

fn zero_value(tds: &Typedefs, ty: &Type) -> Result<String, String> {
    let t = peel(tds, ty);
    match &t.val {
        TypeT::Int { signed, width } => Ok(format!("0{}", int_suffix(*signed, *width)?)),
        TypeT::SizeT => Ok("0sz".to_string()),
        TypeT::Bool => Ok("false".to_string()),
        // C says a pointer zero-initialised by a brace initialiser, by static
        // storage, or by `calloc` is a *null pointer*, not an all-zero object,
        // and Palow's `null` is that pointer. The two happen to agree on the
        // bytes here -- `null_addr` says its address is 0 -- but it is the
        // value that matters, because that is what a comparison with `NULL`
        // will ask about.
        TypeT::Pointer(..) => Ok("null".to_string()),
        TypeT::TypeRef(TypeRefKind::Struct(name)) => {
            let Some(si) = tds.structs.get(&*name.val) else {
                return Err(format!("a zeroed struct {}", name.val));
            };
            let mut vals = Vec::new();
            for f in &si.fields {
                vals.push(match &f.shape {
                    FieldShape::One { .. } => {
                        format!("fld_{} = {}", f.name, zero_value(tds, &f.ty)?)
                    }
                    // There is no zero of a flexible array member: how many
                    // elements there would be is not a fact about the type.
                    FieldShape::Flex { .. } => {
                        return Err(format!("a zeroed flexible array member `{}`", f.name));
                    }
                    // An array field's own type is the array, so the zero has
                    // to be built at the element type and then replicated.
                    FieldShape::Array { len, .. } => {
                        let Some((elem, _)) = flat_array(tds, &f.ty) else {
                            return Err(format!("a zeroed field `{}`", f.name));
                        };
                        format!(
                            "fld_{} = Seq.create {} {}",
                            f.name,
                            len,
                            zero_value(tds, elem)?
                        )
                    }
                });
            }
            Ok(format!("({{ {} }})", vals.join("; ")))
        }
        _ => Err(format!("a zeroed {}", describe(t))),
    }
}

fn binop(tds: &Typedefs, op: BinOp, ty: &Type, signed_ok: bool) -> Result<String, String> {
    let t = peel(tds, ty);
    let m = match &t.val {
        TypeT::Int { signed, width } => {
            format!("{}Int{}", if *signed { "" } else { "U" }, width)
        }
        TypeT::SizeT => "SizeT".to_string(),
        TypeT::PtrdiffT => "Int64".to_string(),
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
                // The one truth test on a pointer C has: `a ?: b` is `a`
                // unless `a` is null. Under Palow that is the only form it
                // could take, a pointer's value not being a number.
                BinOp::Elvis => Ok("`elvis_ptr`".to_string()),
                _ => Err("an operator on a pointer".to_string()),
            };
        }
        // F* already has IEEE-754 arithmetic on `Float32.t`/`Float64.t`, so a
        // C floating-point operator is the corresponding F* one and nothing
        // else: there is no overflow obligation to discharge, because C gives
        // floating-point overflow a value rather than taking the meaning away.
        // `==` is `ieee_eq` and not F* equality: C's `==` identifies `+0.0`
        // with `-0.0` and makes a NaN unequal to itself, and F* equality
        // does neither.
        TypeT::Float {
            width: w @ (32 | 64),
        } => {
            let m = format!("Float{}", w);
            return match op {
                BinOp::Add => Ok(format!("`{}.add`", m)),
                BinOp::Sub => Ok(format!("`{}.sub`", m)),
                BinOp::Mul => Ok(format!("`{}.mul`", m)),
                BinOp::Div => Ok(format!("`{}.div`", m)),
                BinOp::Lt => Ok(format!("`{}.lt`", m)),
                BinOp::LEq => Ok(format!("`{}.lte`", m)),
                BinOp::Eq => Ok(format!("`{}.ieee_eq`", m)),
                _ => Err(format!("an operator on {}", describe(t))),
            };
        }
        _ => return Err(format!("an operator on {}", describe(t))),
    };
    match op {
        BinOp::Eq => return Ok("=".to_string()),
        // GNU `a ?: b`. The operand is already bound to a name by the time
        // this is applied, so the `if` below it duplicates a value and not a
        // computation -- which is the whole content of "evaluated once".
        BinOp::Elvis => {
            return Ok(format!(
                "`elvis_{}`",
                match m.as_str() {
                    "SizeT" => "size_t".to_string(),
                    other => other.to_lowercase(),
                }
            ));
        }
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
/// Where an array subscript's storage lives, and what it takes to put it
/// back. The two closes differ for an array *field*: see `array_place`.
struct ArrayPlace {
    addr: String,
    pn: String,
    esize: String,
    /// A constant element offset into the flat array the address names. Only
    /// a multidimensional array field has one: its outer subscript selects a
    /// row, and a row is not an object of its own but a run of elements of
    /// the same flat sequence.
    base: u64,
    close_read: Vec<String>,
    close_write: Vec<String>,
    maybe: bool,
}

struct Focus {
    at: String,
    pn: String,
    /// Set when the place is a bit-field: the read has to pick the bits out
    /// of the unit that was read, and the write has to put them back into
    /// the unit that is there.
    bits: Option<BitPos>,
    /// The store operation. An element of a local array may not hold a value
    /// yet, so it is written with the write-only operation.
    write_fn: String,
    open_read: Vec<String>,
    open_write: Vec<String>,
    close_read: Vec<String>,
    close_write: Vec<String>,
}

/// Whether an expression is a literal object: a string or compound literal,
/// possibly under the array-to-pointer decay elaboration inserted around it.
fn is_literal(e: &Expr) -> bool {
    match &strip_vattr(e).val {
        ExprT::ArrayInit { .. } => true,
        ExprT::Cast(inner, _) => is_literal(inner),
        _ => false,
    }
}

/// Whether a parameter is `_plain`: a pointer the callee may dereference but
/// holds nothing through. That is the one argument position a literal's
/// address can be passed in, since a literal comes with no ownership at all.
fn is_plain(tds: &Typedefs, ty: &Type) -> bool {
    match &tds.resolve(ty).val {
        TypeT::Plain(_) => true,
        TypeT::Nullable(t) | TypeT::RefineValue(t, ..) => is_plain(tds, t),
        _ => false,
    }
}

/// The lvalue a pointer expression denotes. `&x` names `x` directly, and
/// saying so keeps the ordinary variable path in `store` rather than sending
/// `*(&x)` down the general-pointer one.
fn deref_of(p: &Rc<Expr>) -> Rc<Expr> {
    if let ExprT::Ref(inner) = &strip_vattr(p).val {
        return inner.clone();
    }
    ExprT::Deref(p.clone()).with_loc(p.loc.clone())
}

/// Peel the virtual attributes `elab` wraps around an expression.
/// Substitute an argument for a `_letimpure` accessor's formal in its body.
///
/// Only the forms a specification is written in are covered. Anything else --
/// spliced Pulse above all, whose antiquotations have their own binding rules
/// -- gives `None`, and the caller keeps the error it already had. Inlining a
/// definition the emitter does not fully understand would be exactly the
/// silent weakening this translation is built to avoid.
fn subst_var(e: &Rc<Expr>, from: &str, to: &Rc<Expr>) -> Option<Rc<Expr>> {
    let go = |x: &Rc<Expr>| subst_var(x, from, to);
    let at = |v: ExprT| Some(v.with_loc(e.loc.clone()));
    match &e.val {
        ExprT::Var(v) if &*v.val == from => Some(to.clone()),
        ExprT::Var(_) | ExprT::IntLit(..) | ExprT::BoolLit(_) | ExprT::FloatLit(..) => {
            Some(e.clone())
        }
        ExprT::Deref(x) => at(ExprT::Deref(go(x)?)),
        ExprT::Ref(x) => at(ExprT::Ref(go(x)?)),
        ExprT::Live(x) => at(ExprT::Live(go(x)?)),
        ExprT::Old(x) => at(ExprT::Old(go(x)?)),
        ExprT::Member(x, f) => at(ExprT::Member(go(x)?, f.clone())),
        ExprT::Index(x, i) => at(ExprT::Index(go(x)?, go(i)?)),
        ExprT::VAttr(a, x) => at(ExprT::VAttr(a.clone(), go(x)?)),
        ExprT::UnOp(o, x) => at(ExprT::UnOp(*o, go(x)?)),
        ExprT::BinOp(o, l, r) => at(ExprT::BinOp(*o, go(l)?, go(r)?)),
        ExprT::Cast(x, t) => at(ExprT::Cast(go(x)?, t.clone())),
        ExprT::FnCall(n, xs) => {
            let mut out = Vec::new();
            for x in xs.iter() {
                out.push(go(x)?);
            }
            at(ExprT::FnCall(n.clone(), out.into()))
        }
        _ => None,
    }
}

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

/// The local pointers that are really just another name for a place.
///
/// `int32_t *q = &p->first; *q = v;` gives `q` no storage of its own in C
/// either -- a compiler keeps it in a register, and the object written is
/// `p->first`. Palow cannot model it as an object anyway: doing so would mean
/// holding a focus on `p->first` open from the declaration to the last use,
/// with arbitrary statements in between. Substituting the place at each use
/// avoids the question entirely, and it is what the C means.
///
/// It is only the same C if the place denotes the same object throughout, so
/// the alias is taken only when nothing rebinds the pointer again and nothing
/// rebinds any name the place is built from. Writing *through* those names is
/// fine, and is the whole point.
/// The locals that are another name for an array rather than storage of their
/// own: `T *p = a;` where `a` is itself an array and `p` is never assigned
/// again.
///
/// C's array-to-pointer decay makes this the ordinary way to reach an array
/// through a shorter name, and nothing is copied by it -- `p[i]` and `a[i]`
/// are the same object. Treating `p` as a slot would mean owning a pointer
/// whose pointee is an element of `a`, which is ownership the contract never
/// granted and never had to: it granted the array.
fn array_alias_map(body: &Stmts) -> HashMap<String, String> {
    let mut t = Touched::default();
    touch_stmts(body, &mut t);
    let locals: HashSet<String> = body
        .iter()
        .filter_map(|s| match &s.val {
            StmtT::Decl(n, _) => Some(n.val.to_string()),
            _ => None,
        })
        .collect();
    let mut out: HashMap<String, String> = HashMap::new();
    for st in body.iter() {
        let StmtT::Assign(lhs, rhs) = &st.val else {
            continue;
        };
        let (Some(q), ExprT::Var(a)) = (lvalue_name(lhs), &strip_vattr(rhs).val) else {
            continue;
        };
        // That assignment is the one rebinding of `q`; anything else and `q`
        // is a pointer object whose value changes, which is a different thing
        // entirely.
        if !locals.contains(&q) || t.rebound.get(&q) != Some(&1) {
            continue;
        }
        out.insert(q, a.val.to_string());
    }
    out
}

/// Whether an expression is a pointer or an array, so that adding to it is
/// pointer arithmetic rather than ordinary addition. A type that cannot be
/// inferred here -- a local declared in the body, which this env does not
/// have -- is left alone: the question is only asked to *reject* a sum of
/// two integers, and rejecting more than that would lose real aliases.
fn ptr_base(tds: &Typedefs, env: &Env, e: &Expr) -> bool {
    let Ok(t) = env.infer_expr(e) else {
        return true;
    };
    matches!(
        peel(tds, &t.to_rc()).val,
        TypeT::Pointer(..) | TypeT::FixedArray(..) | TypeT::FlexArray(..)
    )
}

fn alias_map(body: &Stmts, ptr_base: &dyn Fn(&Expr) -> bool) -> HashMap<String, Rc<Expr>> {
    let mut t = Touched::default();
    touch_stmts(body, &mut t);

    let locals: HashSet<String> = body
        .iter()
        .filter_map(|s| match &s.val {
            StmtT::Decl(n, _) => Some(n.val.to_string()),
            _ => None,
        })
        .collect();

    // Every `q = &place` in the body, in order, with a repeated `q` dropped:
    // a pointer assigned twice is an object after all.
    let mut cand: Vec<(String, Rc<Expr>)> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    for st in body.iter() {
        let StmtT::Assign(lhs, rhs) = &st.val else {
            continue;
        };
        let (Some(q), ExprT::Ref(place)) = (lvalue_name(lhs), &strip_vattr(rhs).val) else {
            continue;
        };
        if !locals.contains(&q) {
            continue;
        }
        if !seen.insert(q.clone()) {
            cand.retain(|(n, _)| *n != q);
            continue;
        }
        // The alias assignment is itself the one rebinding of `q`.
        if t.rebound.get(&q) != Some(&1) {
            continue;
        }
        if !matches!(
            &strip_vattr(place).val,
            ExprT::Var(..) | ExprT::Member(..) | ExprT::Index(..)
        ) {
            continue;
        }
        cand.push((q, place.clone()));
    }

    // Taking the address of a *named* object counts as rebinding it, because
    // in general something may store through the address. Here it does not:
    // the address goes to an alias, which is the thing being decided. So each
    // accepted alias pays back the rebinding its own `&` charged. An alias
    // that is then rejected did let the address escape after all, so the
    // discount has to be withdrawn and the rest reconsidered -- hence the
    // fixpoint rather than a single pass.
    loop {
        let mut discount: HashMap<String, usize> = HashMap::new();
        for (_, place) in &cand {
            if let Some(n) = lvalue_name(place) {
                *discount.entry(n).or_insert(0) += 1;
            }
        }
        let before = cand.len();
        cand.retain(|(_, place)| {
            // `&x` for a named object is a fixed address whatever is stored
            // in `x`, so an assignment to `x` is a write to the object the
            // alias already stands for and not a change of which object that
            // is. Only a place computed *through* a name has to ask.
            if matches!(&strip_vattr(place).val, ExprT::Var(..)) {
                return true;
            }
            let mut used = Touched::default();
            touch_expr(place, &mut used);
            // A name the place is built from must denote the same object
            // throughout. Writing *through* it is fine, and is the point.
            used.vars.iter().all(|v| {
                t.rebound.get(v).copied().unwrap_or(0) == discount.get(v).copied().unwrap_or(0)
            })
        });
        if cand.len() == before {
            break;
        }
    }

    // A local that is assigned once from a pointer expression built only out
    // of names the body never rebinds stands for one fixed object for the
    // whole call, so it is an alias too -- of the place that expression
    // dereferences. `struct outer *parent = _container_of(node, struct outer,
    // node);` is the case that matters, and it is the ordinary way C spells
    // the recovery: the recovery itself is a name for the enclosing object,
    // not a pointer variable anyone stores through.
    //
    // No `&` was taken here, so nothing is charged to the fixpoint above and
    // nothing has to be paid back.
    let mut out: HashMap<String, Rc<Expr>> = cand.into_iter().collect();
    for st in body.iter() {
        let StmtT::Assign(lhs, rhs) = &st.val else {
            continue;
        };
        let Some(q) = lvalue_name(lhs) else {
            continue;
        };
        // The one assignment is the whole story: if `q` is written again, or
        // its address is taken, it is an object after all.
        if !locals.contains(&q) || t.rebound.get(&q) != Some(&1) || out.contains_key(&q) {
            continue;
        }
        // `p = a + i` names the element `a[i]`: pointer arithmetic on an array
        // is the index written another way, and a local that holds the result
        // stands for that element as long as nothing rebinds what it was
        // computed from. Spelling it as an index is what lets an access
        // through `p` go down the same path a direct `a[i]` does, instead of
        // needing a dereference rule of its own.
        // The base has to be a pointer or an array for any of that to be
        // true: `int r = a + b;` is addition, and reading `r` as `a[b]` turns
        // a sum into a subscript of something that is not even an object.
        if let ExprT::BinOp(BinOp::Add, base, idx) = &strip_vattr(rhs).val
            && lvalue_name(base).is_some()
            && ptr_base(base)
            && stable_names(rhs, &out, &locals, &t)
        {
            out.insert(
                q,
                ExprT::Index(base.clone(), idx.clone()).with_loc(st.loc.clone()) as Rc<Expr>,
            );
            continue;
        }
        // `q = p` where `p` is itself an alias: a second name for the same
        // place. Copying the place rather than pointing at `p` is what keeps
        // the two names interchangeable.
        if let ExprT::Var(v) = &strip_casts(rhs).val
            && let Some(place) = out.get(&*v.val.to_string()).cloned()
        {
            out.insert(q, place);
            continue;
        }
        if !derived_ptr(rhs) {
            continue;
        }
        if !stable_names(rhs, &out, &locals, &t) {
            continue;
        }
        out.insert(
            q,
            ExprT::Deref(rhs.clone()).with_loc(st.loc.clone()) as Rc<Expr>,
        );
    }
    out
}

/// An expression with its virtual attributes and conversions removed. A
/// pointer that changes type -- `_arrayptr int *` to `int *`, or a cast that
/// only adds `const` -- still names the same place.
fn strip_casts(e: &Expr) -> &Expr {
    match &strip_vattr(e).val {
        ExprT::Cast(inner, _) => strip_casts(inner),
        _ => strip_vattr(e),
    }
}

/// Whether every name an expression is built from denotes the same object for
/// the whole call: a parameter the body never rebinds, or another alias, which
/// is a name for a place and not an object that can be written.
fn stable_names(
    e: &Expr,
    out: &HashMap<String, Rc<Expr>>,
    locals: &HashSet<String>,
    t: &Touched,
) -> bool {
    let mut used = Touched::default();
    touch_expr(e, &mut used);
    used.vars.iter().all(|v| {
        out.contains_key(v) || (!locals.contains(v) && t.rebound.get(v).copied().unwrap_or(0) == 0)
    })
}

/// Whether an expression names an address by arithmetic alone -- no load, no
/// call -- so that it denotes the same object every time it is written.
/// Subtract a field offset from an address, cancelling it syntactically
/// against an addition of the same offset.
///
/// `add_sub_wrap` says the two undo each other, but a lemma is of no help to
/// the frame matcher, which compares addresses as terms and does not call the
/// solver. Casting a pointer out to an initial member and back is exactly this
/// pattern, so the cancellation has to happen in the text.
fn sub_offset(base: String, off: &str) -> String {
    let suffix = format!(" +! {})", off);
    if let Some(inner) = base.strip_prefix('(').and_then(|b| b.strip_suffix(&suffix))
        && balanced(inner)
    {
        return inner.to_string();
    }
    format!("({} -? {})", base, off)
}

/// Whether every parenthesis in `s` is closed within it.
fn balanced(s: &str) -> bool {
    let mut d = 0i32;
    for c in s.chars() {
        match c {
            '(' => d += 1,
            ')' => {
                d -= 1;
                if d < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    d == 0
}

/// Every local pointer assigned exactly once out of memory, with the
/// expression it was loaded from.
///
/// This is *not* an alias: what such a pointer addresses depends on what was
/// stored, so the two are the same object only for as long as nothing writes
/// the source. It is enough for one thing, though -- deciding which piece of
/// deep ownership an access through the local wants opened. Whether the two
/// really are the same address is then left to slprop matching, which is
/// exactly the question it is good at: the load carries a `rewrites_to` to the
/// field's value, and a body that had overwritten the field would be matching
/// against the new value and fail.
fn ptr_source_map(body: &Stmts) -> HashMap<String, Rc<Expr>> {
    let mut t = Touched::default();
    touch_stmts(body, &mut t);
    let locals: HashSet<String> = body
        .iter()
        .filter_map(|s| match &s.val {
            StmtT::Decl(n, _) => Some(n.val.to_string()),
            _ => None,
        })
        .collect();
    let mut out = HashMap::new();
    for st in body.iter() {
        let StmtT::Assign(lhs, rhs) = &st.val else {
            continue;
        };
        let Some(q) = lvalue_name(lhs) else {
            continue;
        };
        if !locals.contains(&q) || t.rebound.get(&q) != Some(&1) {
            continue;
        }
        if !matches!(&strip_vattr(rhs).val, ExprT::Member(..)) {
            continue;
        }
        out.insert(q, rhs.clone());
    }
    out
}

fn derived_ptr(e: &Expr) -> bool {
    match &strip_vattr(e).val {
        ExprT::ContainerOf(inner, _, _) => derived_ptr(inner) || lvalue_name(inner).is_some(),
        ExprT::Cast(inner, _) => derived_ptr(inner),
        _ => false,
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
    forbidden: &HashSet<String>,
    divergent_fns: &HashSet<String>,
) -> Result<TranslatedBody, String> {
    // An array parameter's ownership is a sequence, so every access through it
    // goes through `array_focus` rather than a plain read. Record what each one
    // needs to be focused: the element's Palow type and its size.
    let aliases = alias_map(&defn.body, &|x| ptr_base(tds, &env, x));
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
                addr: format!("var_{}", name.val),
                // An `_out` array arrives as storage, so its elements are
                // `option`s: writing one needs no value to have been there,
                // and reading one is the obligation C says it is.
                maybe: a.mode == ParamMode::Out,
                known_len: false,
            },
        );
    }

    let mut b = Body {
        tds,
        env,
        callees,
        lines: Vec::new(),
        // A granted global is a slot the function did not allocate and must
        // not release. Seeding them first means a local of the same name
        // shadows the global, exactly as C says, because every slot lookup
        // takes the last match.
        slots: sig.globals.clone(),
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
        spec_binders: HashMap::new(),
        ret_binding: None,
        arrays,
        olens: sig.olens.clone(),
        requires_ok: sig.req_props,
        owned: &sig.owned,
        granted: &sig.granted,
        spliced_own: sig.spliced_own,
        guarded: &sig.guarded,
        valid_fps: &sig.valid_fps,
        local_valid_fps: HashSet::new(),
        freeables: &sig.freeables,
        consumed_freed: HashSet::new(),
        consumed: &sig.consumed,
        has_out: defn.decl.args.iter().any(|a| a.mode == ParamMode::Out),
        divergent: false,
        seeded: Vec::new(),
        laundered: HashSet::new(),
        post_valid: &sig.post_valid,
        ret_spliced: sig.ret_spliced,
        gotos: Vec::new(),
        in_loop: false,
        pending_close: Vec::new(),
        open_elems: Vec::new(),
        own_open: Vec::new(),
        loop_mark: None,
        divergent_fns,
        blocks: Vec::new(),
        aliases: aliases,
        ptr_src: ptr_source_map(&defn.body),
        array_aliases: array_alias_map(&defn.body),
        active: HashMap::new(),
        // Only where the contract survived: a dropped `_requires` is not a
        // promise the caller made, so a read resting on it would be resting
        // on nothing.
        live_arms: if sig.contract {
            let mut out = Vec::new();
            for e in &defn.decl.requires {
                active_claims(e, &mut out);
            }
            out
        } else {
            Vec::new()
        },
        uses: HashSet::new(),
        forbidden,
        self_rec: if sig.self_rec {
            Some(defn.decl.name.val.to_string())
        } else {
            None
        },
        params: defn
            .decl
            .args
            .iter()
            .filter_map(|a| a.name.as_ref().map(|n| n.val.to_string()))
            .collect(),
    };

    // A parameter whose address the body takes needs storage, and it needs it
    // for the whole call rather than from the `&` onwards: an `if` arm that
    // writes through the address is writing the object the code after the
    // `if` reads. Doing it here rather than at the first `&` is also what
    // makes that case translatable at all, since a slot allocated inside an
    // arm would be released at the end of it.
    let addressed = {
        let mut t = Touched::default();
        touch_stmts(&defn.body, &mut t);
        t.addressed
    };
    for a in &defn.decl.args {
        let Some(name) = a.name.as_ref() else {
            continue;
        };
        let n = name.val.to_string();
        if a.mode == ParamMode::Out {
            // A single-object `_out` is storage the caller allocated, so it
            // behaves exactly like an uninitialised local: the field writes
            // scatter into it and the last one gathers it back up. The only
            // difference is that the address is the parameter rather than a
            // stack allocation, and that nothing here frees it.
            if extent(tds, &a.ty) == Some(Extent::One)
                && let TypeT::Pointer(pt, _) = &peel(tds, &a.ty).val
                && let Some(pn) = palow_name(tds, pt)
                && let Some(fty) = fstar_type(tds, pt)
                && storable_struct(tds, pt)
            {
                b.slots.push(Slot {
                    name: format!("*{}", n),
                    addr: format!("var_{}", n),
                    palow_ty: pn,
                    fstar_ty: fty,
                    init: false,
                    array: None,
                    // Not ours to release: the caller allocated it.
                    global: true,
                    union_arm: None,
                    filling: None,
                    holds_fn: BTreeMap::new(),
                    scattered: BTreeSet::new(),
                });
            }
            continue;
        }
        if !addressed.contains(&n) || b.arrays.contains_key(&n) {
            continue;
        }
        // A refusal here is not a refusal of the body: the `&` may sit
        // somewhere the translation gives up on anyway, and where it does not
        // the ordinary path reports it with the same words.
        let _ = b.give_storage(&n, &a.ty);
    }

    b.rest(&defn.body)?;
    Ok(TranslatedBody {
        lines: b.lines,
        divergent: b.divergent,
        uses: b.uses,
    })
}

/// Collect every `u.m._active` claim a contract clause makes.
///
/// The walk is over the connectives a contract is built from rather than over
/// every expression: a claim under something else -- an implication, a
/// disjunction -- is not a claim the body may rely on unconditionally, and
/// silently treating it as one would let a read past a guard that does not
/// hold.
fn active_claims(e: &Expr, out: &mut Vec<(Rc<Expr>, String)>) {
    match &e.val {
        ExprT::VAttr(VAttr::Active(m), obj) => out.push((obj.clone(), m.val.to_string())),
        ExprT::Cast(x, _) => active_claims(x, out),
        // `p == true` is how a `_Bool`-valued clause arrives, and `&&` is a
        // conjunction of claims: both halves hold.
        ExprT::BinOp(BinOp::LogAnd, l, r) => {
            active_claims(l, out);
            active_claims(r, out);
        }
        ExprT::BinOp(BinOp::Eq, l, r) => {
            if matches!(&strip_vattr(r).val, ExprT::BoolLit(true)) {
                active_claims(l, out);
            }
            if matches!(&strip_vattr(l).val, ExprT::BoolLit(true)) {
                active_claims(r, out);
            }
        }
        _ => {}
    }
}

/// Whether two lvalue expressions name the same object, ignoring the
/// annotations elaboration leaves behind. This is deliberately syntactic:
/// two spellings that happen to denote the same object -- a pointer copied
/// into a local, say -- are not matched, because deciding that is aliasing
/// reasoning and not something a comparison of trees can do.
fn same_lvalue(a: &Expr, b: &Expr) -> bool {
    match (&strip_vattr(a).val, &strip_vattr(b).val) {
        (ExprT::Var(x), ExprT::Var(y)) => x.val == y.val,
        (ExprT::Deref(x), ExprT::Deref(y)) => same_lvalue(x, y),
        (ExprT::Member(x, f), ExprT::Member(y, g)) => f.val == g.val && same_lvalue(x, y),
        _ => false,
    }
}

/// Whether a C block always leaves the function, so that whatever follows it
/// is reached only on the other path. Statements after a `return` are
/// unreachable, so their shape does not matter.
/// Whether a proposition says nothing but that some storage exists. A label's
/// `_ensures` is usually exactly that, and the slots carry it already.
fn live_only(e: &Expr) -> bool {
    match &strip_vattr(e).val {
        ExprT::Live(_) => true,
        ExprT::Cast(inner, _) => live_only(inner),
        ExprT::BinOp(BinOp::LogAnd, a, b) => live_only(a) && live_only(b),
        _ => false,
    }
}

/// A literal integer, through the casts a C literal arrives wrapped in.
fn int_lit(e: &Expr) -> Option<u64> {
    match &strip_vattr(e).val {
        ExprT::IntLit(k, _) => u64::try_from(&**k).ok(),
        ExprT::Cast(inner, _) => int_lit(inner),
        _ => None,
    }
}

fn is_zero(e: &Expr) -> bool {
    int_lit(e) == Some(0)
}

fn returns(stmts: &Stmts) -> bool {
    stmts.iter().any(|s| match &s.val {
        // A `goto` leaves this block too: what follows it in the block is
        // reached only on the path that did not jump, which is the same thing
        // an early `return` means one level further out.
        StmtT::Return(_) | StmtT::Goto(_) => true,
        // An `if` both of whose arms leave is a block that leaves, and that
        // is how a chain of early returns ends up being one.
        StmtT::If {
            then_branch,
            else_branch,
            ..
        } => returns(then_branch) && returns(else_branch),
        _ => false,
    })
}

/// Names for the constructs the subset does not cover. These end up in the
/// generated file next to each `admit()`, which is what turns it into a list
/// of what to do next rather than a list of failures.
/// Whether a ghost statement only seeds or drops a fact about the existing
/// function-pointer model, which Palow supplies for itself.
/// The head of a ghost statement: the dotted name it applies, which is
/// everything up to the first antiquotation.
/// An `_include_pulse` block: hand-written Pulse at the top level.
///
/// There is no function here, so there are no C objects to read and no
/// addresses to take. What an antiquotation can mention is a `$declare`d name
/// -- a binder the fragment introduces itself and then uses as if it were a C
/// value -- and the generated names for types and fields.
fn include_pulse(tds: &Typedefs, code: &InlinePulseCode) -> Result<String, String> {
    let mut declared: HashMap<String, Rc<Type>> = HashMap::new();
    include_pulse_scoped(tds, &mut declared, code)
}

/// The same, with the `$declare`d binders of an enclosing fragment already in
/// scope. A fragment nested inside an antiquotation -- the `PL_Engine uds` in
/// `$(context_full_pred(s, _inline_pulse(PL_Engine uds)))` -- is written in
/// the enclosing fragment's vocabulary, so it is spliced in the enclosing
/// fragment's scope.
fn include_pulse_scoped(
    tds: &Typedefs,
    declared: &mut HashMap<String, Rc<Type>>,
    code: &InlinePulseCode,
) -> Result<String, String> {
    let mut out = String::new();
    for tok in &code.tokens {
        match tok {
            InlinePulseToken::Verbatim(ct) => {
                out.push_str(ct.before);
                out.push_str(&ct.text.val);
            }
            InlinePulseToken::Declare { ident, ty } => {
                declared.insert(ident.val.to_string(), ty.clone());
            }
            InlinePulseToken::RValueAntiquot { before, expr }
            | InlinePulseToken::LValueAntiquot { before, expr } => {
                let v = declared_expr(tds, declared, expr)?;
                out.push_str(before);
                // A bare name needs no parentheses, and in a *binder* --
                // `($(s): $type(context_t))` -- it must not have any: F*
                // reads `((s): t)` as a pattern, not as a binding.
                if v.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    out.push_str(&v);
                } else {
                    out.push_str(&format!("({})", v));
                }
            }
            InlinePulseToken::TypeAntiquot { before, ty } => {
                let t =
                    fstar_type(tds, ty).ok_or_else(|| format!("`$type` of {}", describe(ty)))?;
                out.push_str(before);
                out.push_str(&format!("({})", t));
            }
            InlinePulseToken::FieldAntiquot {
                before,
                ty,
                field_name,
            } => {
                out.push_str(before);
                out.push_str(&field_antiquot(tds, ty, field_name)?);
            }
            InlinePulseToken::AuxFnAntiquot { kind, .. } => {
                return Err(format!(
                    "`${}`, which names a helper of the old memory model",
                    kind.keyword()
                ));
            }
        }
    }
    Ok(out)
}

/// The generated name a `$field` stands for: a record field of a struct, or
/// the constructor of a union member.
/// A spliced fragment is dropped into a `requires`/`ensures` clause or into
/// the middle of a statement, and Pulse reads indentation, so a fragment that
/// was written across several lines has to become one line before it lands
/// somewhere its original column no longer means anything. A line comment
/// would swallow the rest of the term, so a fragment carrying one is refused
/// rather than silently mangled.
fn flatten_fragment(s: &str) -> Result<String, String> {
    if s.contains("//") {
        return Err("inline Pulse containing a line comment".to_string());
    }
    let mut out = String::new();
    for (i, line) in s.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if i > 0 && !out.is_empty() {
            out.push(' ');
        }
        out.push_str(line);
    }
    Ok(out)
}

fn field_antiquot(tds: &Typedefs, ty: &Type, field_name: &Ident) -> Result<String, String> {
    match &peel(tds, ty).val {
        TypeT::TypeRef(TypeRefKind::Struct(_)) => Ok(format!("fld_{}", field_name)),
        TypeT::TypeRef(TypeRefKind::Union(u)) => Ok(format!("Union_{}_{}", u.val, field_name)),
        _ => Err(format!("`$field` of {}", describe(ty))),
    }
}

/// A pure expression rooted at a `$declare`d binder.
fn declared_expr(
    tds: &Typedefs,
    declared: &HashMap<String, Rc<Type>>,
    e: &Expr,
) -> Result<String, String> {
    match &e.val {
        ExprT::Var(v) if declared.contains_key(&v.val.to_string()) => Ok(v.val.to_string()),
        ExprT::Member(b, f) => {
            let bt = declared_type(tds, declared, b)?;
            Ok(match &peel(tds, &bt).val {
                TypeT::TypeRef(TypeRefKind::Union(u)) => format!(
                    "Union_{}_{}?.v {}",
                    u.val,
                    f.val,
                    declared_expr(tds, declared, b)?
                ),
                _ => field_value(
                    tds,
                    &bt,
                    &declared_expr(tds, declared, b)?,
                    &f.val.to_string(),
                ),
            })
        }
        // `u.m._active` asks which member is live, which for a tagged value is
        // simply which constructor it was built with.
        ExprT::Cast(inner, _) => declared_expr(tds, declared, inner),
        // A `_let` is an ordinary F* definition, so a hand-written fragment
        // can name it just as a contract can. That is what lets the ghost
        // helpers of a model be stated in terms of the same predicate the
        // contracts use, instead of restating it.
        ExprT::FnCall(name, args) if tds.pure_fns.contains(&*name.val.to_string()) => {
            let mut out = format!("func_{}", name.val);
            for a in args.iter() {
                out += &format!(" ({})", declared_expr(tds, declared, a)?);
            }
            if args.is_empty() {
                out += " ()";
            }
            Ok(out)
        }
        ExprT::InlinePulse(code, _) => {
            let mut d = declared.clone();
            flatten_fragment(&include_pulse_scoped(tds, &mut d, code)?)
        }
        ExprT::VAttr(a, b) => {
            let VAttr::Active(m) = a else {
                return Err("a `_length` outside a function".to_string());
            };
            let bt = declared_type(tds, declared, b)?;
            let TypeT::TypeRef(TypeRefKind::Union(u)) = &peel(tds, &bt).val else {
                return Err("`_active` on something that is not a union".to_string());
            };
            Ok(format!(
                "Union_{}_{}? ({})",
                u.val,
                m.val,
                declared_expr(tds, declared, b)?
            ))
        }
        _ => Err(format!(
            "{}, which an antiquotation cannot stand for here",
            expr_kind(e)
        )),
    }
}

/// The C type of a pure expression rooted at a `$declare`d binder.
fn declared_type(
    tds: &Typedefs,
    declared: &HashMap<String, Rc<Type>>,
    e: &Expr,
) -> Result<Rc<Type>, String> {
    match &e.val {
        ExprT::Var(v) => declared
            .get(&v.val.to_string())
            .cloned()
            .ok_or_else(|| format!("`{}`, which is not `$declare`d", v.val)),
        ExprT::Member(b, f) => {
            let bt = declared_type(tds, declared, b)?;
            let fs: Vec<_> = match &peel(tds, &bt).val {
                TypeT::TypeRef(TypeRefKind::Struct(n)) => tds
                    .structs
                    .get(&*n.val.to_string())
                    .map(|si| {
                        si.fields
                            .iter()
                            .map(|x| (x.name.clone(), x.ty.clone()))
                            .collect()
                    })
                    .unwrap_or_default(),
                TypeT::TypeRef(TypeRefKind::Union(n)) => tds
                    .unions
                    .get(&*n.val.to_string())
                    .map(|ui| {
                        ui.members
                            .iter()
                            .map(|x| (x.name.clone(), x.ty.clone()))
                            .collect()
                    })
                    .unwrap_or_default(),
                _ => return Err(format!("a member of {}", describe(&bt))),
            };
            fs.into_iter()
                .find(|(n, _)| *n == *f.val.to_string())
                .map(|(_, t)| t)
                .ok_or_else(|| format!("field `{}`", f.val))
        }
        ExprT::VAttr(_, b) => declared_type(tds, declared, b),
        _ => Err("an antiquotation that is not a `$declare`d name".to_string()),
    }
}

fn ghost_head(code: &InlinePulseCode) -> String {
    let mut head = String::new();
    for t in &code.tokens {
        let InlinePulseToken::Verbatim(tok) = t else {
            break;
        };
        head.push_str(&tok.text.val);
    }
    head
}

/// The aux-function antiquotation a ghost statement applies, if it is one.
///
/// Only a statement that *opens* with the antiquotation counts: one that
/// merely mentions it somewhere in an argument is saying something else.
fn aux_fn_kind(code: &InlinePulseCode) -> Option<AuxFnKind> {
    match code.tokens.first() {
        Some(InlinePulseToken::AuxFnAntiquot { kind, before, .. }) if before.trim().is_empty() => {
            Some(*kind)
        }
        _ => None,
    }
}

/// The union type, arm and object of an `$activate`, if that is what this
/// statement is.
fn aux_activate(code: &InlinePulseCode) -> Option<(&Type, &Ident, &Expr)> {
    let (ty, arm) = match code.tokens.first() {
        Some(InlinePulseToken::AuxFnAntiquot {
            kind: AuxFnKind::Activate,
            before,
            ty,
            field_name: Some(arm),
        }) if before.trim().is_empty() => (ty, arm),
        _ => return None,
    };
    let obj = code.tokens.iter().find_map(|t| match t {
        InlinePulseToken::RValueAntiquot { expr, .. }
        | InlinePulseToken::LValueAntiquot { expr, .. } => Some(&**expr),
        _ => None,
    })?;
    Some((ty, arm, obj))
}

/// The object a `$unfold-uninit` opens, if that is what this statement is.
///
/// The old model's uninitialised-open takes exactly one argument, the object,
/// and it arrives as the first antiquotation after the head.
fn uninit_open_arg(code: &InlinePulseCode) -> Option<&Expr> {
    if !matches!(aux_fn_kind(code), Some(AuxFnKind::UnfoldUninit))
        && !ghost_head(code).contains("__aux_raw_unfold_uninit")
    {
        return None;
    }
    code.tokens.iter().find_map(|t| match t {
        InlinePulseToken::RValueAntiquot { expr, .. }
        | InlinePulseToken::LValueAntiquot { expr, .. } => Some(&**expr),
        _ => None,
    })
}

/// Whether a ghost statement is about a part of the *old* memory model that
/// Palow replaces with something the emitter writes itself.
///
/// Dropping a proof hint is sound in one direction only, and it is the safe
/// one: a hint can make a proof succeed that would otherwise fail, so removing
/// one can only cause a failure, never let a wrong proof through. What makes
/// it right rather than merely safe is that for each of these the emitter
/// already writes the replacement:
///
///   * the old function-pointer model -- Palow emits `of_fn_div_valid` before
///     an indirect call and `drop_is_valid` after it;
///   * the array-cell borrow discipline -- Palow has no `_arrayptr` and no
///     borrowed cell, only `array_focus`/`array_unfocus` around each access;
///   * the maybe-uninitialised discipline -- Palow writes `write_uninit` and
///     `forget` where the initialisation state changes;
///   * acquiring a global's storage, and the `drop_` that releases it again --
///     in Palow a global's ownership arrives in the contract, so there is
///     nothing to acquire and nothing to give back;
///   * opening a struct into one reference per field, which the old model
///     needs before it can touch a field at all -- Palow addresses a field as
///     the object's address plus an offset, and the emitter writes the
///     `focus`/`unfocus` pair around each access itself, so there is nothing
///     to open.
///
/// Every other ghost statement says something Palow has no other way to learn,
/// and is still refused rather than silently discarded.
fn ghost_replaced(code: &InlinePulseCode) -> bool {
    let head = ghost_head(code);
    const REPLACED: &[&str] = &[
        "Pulse.Lib.C.FuncPtr.",
        "arrayptr_drop",
        "array_borrow_cell",
        "array_cell_read",
        "array_return_cell",
        "Pulse.Lib.C.MaybeUninit.",
    ];
    if REPLACED.iter().any(|p| head.starts_with(p)) {
        return true;
    }
    // `$unfold`/`$fold` and their uninitialised variants, whether the source
    // wrote the antiquotation or the generated name it stands for.
    if head.contains("__aux_raw_unfold") || head.contains("__aux_raw_fold") {
        return true;
    }
    if matches!(
        aux_fn_kind(code),
        Some(AuxFnKind::Unfold | AuxFnKind::UnfoldUninit | AuxFnKind::Fold | AuxFnKind::FoldUninit)
    ) {
        return true;
    }
    if head.starts_with("Global_") && head.contains(".acquire_var_") {
        return true;
    }
    // The matching release. `drop_` on its own says nothing about which model
    // it belongs to, so the global's address has to appear in it.
    head.starts_with("drop_")
        && code.tokens.iter().any(|t| match t {
            InlinePulseToken::Verbatim(tok) => tok.text.val.contains("addr_var_"),
            _ => false,
        })
}

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
