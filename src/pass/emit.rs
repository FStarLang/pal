use std::fmt::Write;
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use ::pretty::{RcDoc, Render, RenderAnnotated};
use num_bigint::BigInt;

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    env::{Env, LocalDecl, LocalDeclKind},
    ir::*,
    mayberc::MaybeRc,
};

pub type SourceRangeMap = Vec<(Location, Range)>;

/// Normalize a possibly-negative integer literal into the unsigned range
/// [0, 2^width).
///
/// clang hands us the signed interpretation of an N-bit bit pattern (see
/// `toBigInt` in `cpp/impl.cpp`, which uses `toStringSigned`), so an unsigned
/// literal with the high bit set arrives as a negative `BigInt` (e.g. the u32
/// value 0xFFFFFFFF as -1). F* unsigned literals must be non-negative, so we
/// reduce the value modulo 2^width before emitting it.
fn normalize_unsigned(val: &BigInt, width: u32) -> BigInt {
    let modulus = BigInt::from(1u32) << width;
    ((val % &modulus) + &modulus) % &modulus
}

/// The module holding a function's fnptr wrapper (`func_<g>__fp`), whose type
/// carries the inlined pre/post spec. Kept separate from the function's own
/// module `Func_<g>` so the wrapper is only materialized as its own artifact
/// when the function's address is taken.
fn funcptr_module_name(g: &str) -> String {
    format!("Funcptr_{}", g)
}

/// Determines the output module name for a given top-level declaration.
pub fn module_name_for_decl(decl: &Decl) -> String {
    match &decl.val {
        DeclT::FnDefn(fn_defn) => format!("Func_{}", fn_defn.decl.name.val),
        DeclT::FnDecl(fn_decl) => format!("Func_{}", fn_decl.name.val),
        DeclT::Typedef(type_defn) => format!("Typedef_{}", type_defn.name.val),
        DeclT::StructDefn(struct_defn) => format!("Struct_{}", struct_defn.name.val),
        DeclT::StructDecl(name) => format!("Struct_{}", name.val),
        DeclT::UnionDefn(union_defn) => format!("Union_{}", union_defn.name.val),
        DeclT::IncludeDecl(include_decl) => include_decl.module_name.to_string(),
        DeclT::LetDecl(let_decl) => format!("Let_{}", let_decl.name.val),
        DeclT::OpaqueTypeDecl(decl) => format!("Type_{}", decl.name.val),
        DeclT::GlobalVar(gv) => format!("Global_{}", gv.name.val),
    }
}

/// Extracts the raw C declaration name (identifier) from a Decl.
pub fn decl_name(decl: &Decl) -> String {
    match &decl.val {
        DeclT::FnDefn(fn_defn) => fn_defn.decl.name.val.to_string(),
        DeclT::FnDecl(fn_decl) => fn_decl.name.val.to_string(),
        DeclT::Typedef(type_defn) => type_defn.name.val.to_string(),
        DeclT::StructDefn(struct_defn) => struct_defn.name.val.to_string(),
        DeclT::StructDecl(name) => name.val.to_string(),
        DeclT::UnionDefn(union_defn) => union_defn.name.val.to_string(),
        DeclT::IncludeDecl(include_decl) => include_decl.module_name.to_string(),
        DeclT::LetDecl(let_decl) => let_decl.name.val.to_string(),
        DeclT::OpaqueTypeDecl(decl) => decl.name.val.to_string(),
        DeclT::GlobalVar(gv) => gv.name.val.to_string(),
    }
}

/// Determines the module name that would contain a given Name reference.
fn module_for_name(name: &Name) -> Option<String> {
    match name {
        // Name::Fn is handled via fn_module_map in Emitter::emit_name
        Name::Fn(_) => None,
        Name::TypeRef(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRef(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRef(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::TypeRefPred(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefPred(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefPred(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::TypeRefUninitPred(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefUninitPred(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefUninitPred(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::StructFieldProj(s, _) => Some(format!("Struct_{}", s)),
        Name::StructDirectFieldName(s, _) => Some(format!("Struct_{}", s)),
        Name::StructGhostFieldProj(s, _) => Some(format!("Struct_{}", s)),
        Name::StructAuxFn(s, _) => Some(format!("Struct_{}", s)),
        Name::StructContainerFn(s, _) => Some(format!("Struct_{}", s)),
        Name::StructContainerInv(s, _) => Some(format!("Struct_{}", s)),
        Name::StructProjContainerInv(s, _) => Some(format!("Struct_{}", s)),
        Name::StructProjNull(s, _) => Some(format!("Struct_{}", s)),
        Name::UnionFieldConstructor(u, _) => Some(format!("Union_{}", u)),
        Name::UnionGhostFieldProj(u, _) => Some(format!("Union_{}", u)),
        Name::UnionFieldProj(u, _) => Some(format!("Union_{}", u)),
        Name::UnionAuxFn(u, _, _) => Some(format!("Union_{}", u)),
        Name::UnionActivateFn(u, _) => Some(format!("Union_{}", u)),
        Name::TypeRefDefault(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefDefault(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefDefault(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::TypeRefSpec(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefSpec(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefSpec(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::TypeRefSpecField(TypeRef::Struct(s), _) => Some(format!("Struct_{}", s)),
        Name::TypeRefSpecField(TypeRef::Union(u), _) => Some(format!("Union_{}", u)),
        Name::TypeRefSpecField(TypeRef::Typedef(t), _) => Some(format!("Typedef_{}", t)),
        Name::TypeRefPredUnfold(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefPredUnfold(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefPredUnfold(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::TypeRefPredFold(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefPredFold(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefPredFold(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        Name::TypeRefSizeofPos(TypeRef::Struct(s)) => Some(format!("Struct_{}", s)),
        Name::TypeRefSizeofPos(TypeRef::Union(u)) => Some(format!("Union_{}", u)),
        Name::TypeRefSizeofPos(TypeRef::Typedef(t)) => Some(format!("Typedef_{}", t)),
        // Global address names live in the global's own module.
        Name::GlobalAddr(v) | Name::GlobalAddrNotNull(v) | Name::GlobalAcquire(v) => {
            Some(format!("Global_{}", v))
        }
        // Local names (Var, Val, Perm) are not cross-module references
        Name::Var(_) | Name::Val(_, _) | Name::Perm(_, _) => None,
    }
}

/// Builds a map from function/let/global/opaque-type identifiers to their owning module name.
/// This is needed because Name::Fn is used for all function-like references (FnDefn, LetDecl, etc.)
/// but they live in different module prefixes.
fn build_fn_module_map(decls: &[Decl]) -> HashMap<Rc<str>, String> {
    let mut map = HashMap::new();
    for decl in decls {
        match &decl.val {
            DeclT::FnDefn(fn_defn) => {
                let m = format!("Func_{}", fn_defn.decl.name.val);
                let n = &fn_defn.decl.name.val;
                // Register the synthetic fnptr wrapper name so indirect calls in
                // other modules qualify it to its defining module. The wrapper
                // lives in its own `Funcptr_<g>` module (emitted only when the
                // function's address is taken), not in `Func_<g>`. The pre/post
                // are no longer named declarations (they are inlined into the
                // wrapper's type and recovered via `pre_of`/`post_of`).
                let fp = funcptr_module_name(n);
                map.insert(Rc::from(format!("{}__fp", n)), fp);
                map.insert(fn_defn.decl.name.val.clone(), m);
            }
            DeclT::FnDecl(fn_decl) => {
                let m = format!("Func_{}", fn_decl.name.val);
                let n = &fn_decl.name.val;
                // A declaration can be address-taken too, and its wrapper lives
                // in `Funcptr_<g>` just as above.
                let fp = funcptr_module_name(n);
                map.insert(Rc::from(format!("{}__fp", n)), fp);
                map.insert(fn_decl.name.val.clone(), m);
            }
            DeclT::LetDecl(let_decl) => {
                map.insert(
                    let_decl.name.val.clone(),
                    format!("Let_{}", let_decl.name.val),
                );
            }
            DeclT::OpaqueTypeDecl(decl) => {
                map.insert(decl.name.val.clone(), format!("Type_{}", decl.name.val));
            }
            DeclT::GlobalVar(gv) => {
                map.insert(gv.name.val.clone(), format!("Global_{}", gv.name.val));
            }
            _ => {}
        }
    }
    map
}

/// Builds a map from typedef names that are actually OpaqueTypeDecls to their `Type_*` module.
/// This overrides the default `Typedef_*` mapping from module_for_name for TypeRef lookups.
fn build_typedef_override_map(decls: &[Decl]) -> HashMap<Rc<str>, String> {
    let mut map = HashMap::new();
    for decl in decls {
        if let DeclT::OpaqueTypeDecl(d) = &decl.val {
            map.insert(d.name.val.clone(), format!("Type_{}", d.name.val));
        }
    }
    map
}

type Annotation = Rc<SourceInfo>;
type Doc = RcDoc<'static, Annotation>;

/// The generated pieces of a function-pointer contract spec: the inlined
/// pre/post `slprop` expressions (`pre_expr`/`post_expr`, spliced directly
/// into the `__fp` wrapper's `requires`/`ensures`) plus the wrapper name and
/// callee, used by the address-taken wrapper (`emit_fnptr_triple`).
struct FnPtrSpecCore {
    pre_expr: Doc,
    post_expr: Doc,
    wrap_name: Doc,
    callee: Doc,
    domain: Doc,
    ret_name: Doc,
    ret_ty_doc: Doc,
    projs: Vec<Doc>,
}

/// Tracks whether an emitted expression is an F* lvalue (ref a) or rvalue (a).
enum ExprKind {
    LValue(Doc),      // ref a
    ArrayLValue(Doc), // array elem (when a = array_spec elem)
    RValue(Doc),      // a
}

impl ExprKind {
    /// Convert to an rvalue (F* type `a`). Dereferences lvalues with `!`.
    fn to_rvalue(self) -> Doc {
        match self {
            ExprKind::LValue(doc) => parens(Doc::text("!").append(doc)),
            ExprKind::ArrayLValue(doc) => unaryfn(Doc::text("array_read_all"), doc),
            ExprKind::RValue(doc) => doc,
        }
    }

    /// Convert to an rvalue with C-style array-to-pointer decay.
    ///
    /// In C, an inline array used in rvalue context decays to a pointer to
    /// its first element — i.e. yields the bare array handle, not the
    /// contents. This is the correct conversion for every rvalue use of an
    /// inline-array field projection (assignment RHS, function-call args,
    /// return values, requires/ensures, etc.). Distinct from `to_rvalue`,
    /// which wraps `ArrayLValue` in `array_read_all` and returns
    /// `array_spec T` — only correct if a caller genuinely wants the
    /// contents (currently no emit site does).
    fn to_rvalue_decayed(self) -> Doc {
        match self {
            ExprKind::LValue(doc) => parens(Doc::text("!").append(doc)),
            ExprKind::ArrayLValue(doc) => doc,
            ExprKind::RValue(doc) => doc,
        }
    }

    /// Extract the raw document without rvalue/lvalue conversion.
    fn into_doc(self) -> Doc {
        match self {
            ExprKind::LValue(doc) | ExprKind::ArrayLValue(doc) | ExprKind::RValue(doc) => doc,
        }
    }
}

struct StrWriter {
    buffer: String,
    line: usize,
    character: usize,

    source_range_map: SourceRangeMap,
    annotation_stack: Vec<(Annotation, Position)>,
}
impl StrWriter {
    fn new() -> StrWriter {
        StrWriter {
            buffer: String::default(),
            line: 0,
            character: 0,
            source_range_map: vec![],
            annotation_stack: vec![],
        }
    }
    fn cur_pos(&self) -> Position {
        Position {
            line: self.line as u32 + 1,
            character: self.character as u32 + 1,
        }
    }
}
impl Render for StrWriter {
    type Error = ();

    fn write_str(&mut self, s: &str) -> Result<usize, Self::Error> {
        self.buffer.push_str(s);

        let mut first = true;
        for line in s.split('\n') {
            if first {
                first = false
            } else {
                self.line += 1;
                self.character = 0;
            }
            self.character += line.len();
        }

        Ok(s.len())
    }

    fn fail_doc(&self) -> Self::Error {
        ()
    }
}
impl<'a> RenderAnnotated<'a, Annotation> for StrWriter {
    fn push_annotation(&mut self, annotation: &'a Annotation) -> Result<(), Self::Error> {
        self.annotation_stack
            .push((annotation.clone(), self.cur_pos()));
        Ok(())
    }

    fn pop_annotation(&mut self) -> Result<(), Self::Error> {
        let (loc, start) = self.annotation_stack.pop().unwrap();
        self.source_range_map.push((
            loc.location().clone(),
            Range {
                start,
                end: self.cur_pos(),
            },
        ));
        Ok(())
    }
}

fn annotated<T>(ast: &Ast<T>, doc: impl FnOnce() -> Doc) -> Doc {
    doc().annotate(ast.loc.clone())
}

fn parens(doc: Doc) -> Doc {
    Doc::text("(")
        .append(doc)
        .append(Doc::text(")"))
        .nest(2)
        .group()
}

fn unaryfn(f: Doc, arg: Doc) -> Doc {
    parens(f.append(Doc::line()).append(arg))
}

fn naryfn<T: IntoIterator<Item = Doc>>(args: T) -> Doc {
    parens(Doc::intersperse(args.into_iter(), Doc::line()))
}

fn nary_no_parens<T: IntoIterator<Item = Doc>>(args: T) -> Doc {
    Doc::intersperse(args.into_iter(), Doc::space())
}

// Many F* functions encode their specifications as refinements in the return type.
// This breaks type inference in interesting ways, so we wrap it in `id #desired_type ...`.
// Note: `(... <: desired_type)` doesn't work as well since it is normalized somewhere.
fn with_type(t: Doc, ty: Doc) -> Doc {
    naryfn([Doc::text("id"), Doc::text("#").append(ty), t])
}

fn unaryfn_with_type(f: Doc, arg: Doc, ty: Doc) -> Doc {
    with_type(unaryfn(f, arg), ty)
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum TypeRef {
    Typedef(Rc<IdentT>),
    Struct(Rc<IdentT>),
    Union(Rc<IdentT>),
}
impl From<&TypeRefKind> for TypeRef {
    fn from(tr: &TypeRefKind) -> Self {
        match tr {
            TypeRefKind::Typedef(t) => TypeRef::Typedef(t.val.clone()),
            TypeRefKind::Struct(s) => TypeRef::Struct(s.val.clone()),
            TypeRefKind::Union(u) => TypeRef::Union(u.val.clone()),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Name {
    Var(Rc<IdentT>),
    /// The address of a `_pure` global: an assumed `ref` naming its storage,
    /// one per global, so distinct globals get distinct addresses.
    GlobalAddr(Rc<IdentT>),
    /// Proof that a global's address is non-NULL.
    GlobalAddrNotNull(Rc<IdentT>),
    /// Acquires *read-only* ownership of a global's storage. Called in the
    /// prologue of every function that takes the global's address.
    GlobalAcquire(Rc<IdentT>),
    Val(Rc<IdentT>, u32),
    Perm(Rc<IdentT>, u32),
    Fn(Rc<IdentT>),
    TypeRef(TypeRef),
    TypeRefPred(TypeRef),
    TypeRefUninitPred(TypeRef),

    TypeRefSpec(TypeRef),
    TypeRefSpecField(TypeRef, String),
    TypeRefPredUnfold(TypeRef),
    TypeRefPredFold(TypeRef),
    TypeRefSizeofPos(TypeRef),

    StructFieldProj(Rc<IdentT>, Rc<IdentT>),
    StructDirectFieldName(Rc<IdentT>, Rc<IdentT>),
    StructGhostFieldProj(Rc<IdentT>, Rc<IdentT>),
    StructAuxFn(Rc<IdentT>, String),
    /// Inverse of the field-address projection: maps a `ref` of an embedded
    /// (by-value) struct/union field back to a `ref` of the enclosing struct.
    StructContainerFn(Rc<IdentT>, Rc<IdentT>),
    /// Left-inverse lemma tying `StructContainerFn` to `StructGhostFieldProj`.
    StructContainerInv(Rc<IdentT>, Rc<IdentT>),
    /// Right-inverse (dual) lemma: `proj (container r) == r`. Lets a caller that
    /// owns a struct *via* `container_of(field_ref)` still address the field
    /// through the original `field_ref`.
    StructProjContainerInv(Rc<IdentT>, Rc<IdentT>),
    /// Ground axiom `proj (null #outer) == null #inner` for the offset-0 member:
    /// `container_of` on a struct's first field is pointer identity, so the
    /// field projection maps the null enclosing pointer to the null inner one.
    /// The dual `container (null #inner) == null #outer` is not emitted: it
    /// follows from `StructContainerInv` at `p = null`.
    StructProjNull(Rc<IdentT>, Rc<IdentT>),

    UnionFieldConstructor(Rc<IdentT>, Rc<IdentT>),
    UnionGhostFieldProj(Rc<IdentT>, Rc<IdentT>),
    UnionFieldProj(Rc<IdentT>, Rc<IdentT>),
    UnionAuxFn(Rc<IdentT>, &'static str, Rc<IdentT>),
    /// Ghost axiom (`assume val ... : stt_ghost ...`) that activates a union
    /// arm, used before a partial sub-field write `u->arm.field = v`.
    UnionActivateFn(Rc<IdentT>, Rc<IdentT>),

    TypeRefDefault(TypeRef),
}
impl Name {
    fn to_string(&self) -> String {
        fn struct_to_string(ident: &Rc<IdentT>) -> String {
            Name::TypeRef(TypeRef::Struct(ident.clone())).to_string()
        }
        fn union_to_string(ident: &Rc<IdentT>) -> String {
            Name::TypeRef(TypeRef::Union(ident.clone())).to_string()
        }
        fn typeref_to_string(typeref: &TypeRef) -> String {
            Name::TypeRef(typeref.clone()).to_string()
        }

        match self {
            Name::Var(v) => {
                let v: &str = v;
                match v {
                    "this" | "return" => v.into(),
                    _ => format!("var_{}", v),
                }
            }
            Name::GlobalAddr(v) => format!("addr_var_{}", v),
            Name::GlobalAddrNotNull(v) => format!("addr_var_{}_not_null", v),
            Name::GlobalAcquire(v) => format!("acquire_var_{}", v),
            Name::Val(v, idx) => {
                let v: &str = v;
                format!("val_{}_{}", v, idx)
            }
            Name::Perm(v, idx) => {
                let v: &str = v;
                format!("p_{}_{}", v, idx)
            }
            Name::Fn(v) => format!("func_{}", v),
            Name::TypeRef(TypeRef::Struct(str)) => format!("struct_{}", str),
            Name::TypeRef(TypeRef::Union(str)) => format!("union_{}", str),
            Name::TypeRef(TypeRef::Typedef(ty)) => format!("ty_{}", ty),
            Name::TypeRefPred(type_ref) => format!("{}__pred", typeref_to_string(type_ref)),
            Name::TypeRefPredUnfold(type_ref) => {
                format!("{}__pred_unfold", typeref_to_string(type_ref))
            }
            Name::TypeRefPredFold(type_ref) => {
                format!("{}__pred_fold", typeref_to_string(type_ref))
            }
            Name::TypeRefSizeofPos(type_ref) => {
                format!("{}__sizeof_pos", typeref_to_string(type_ref))
            }
            Name::TypeRefSpec(type_ref) => format!("{}__spec", typeref_to_string(type_ref)),
            Name::TypeRefSpecField(type_ref, fld) => {
                format!("{}__spec__{}", typeref_to_string(type_ref), fld)
            }
            Name::TypeRefUninitPred(type_ref) => {
                format!("{}__uninit_pred", typeref_to_string(type_ref))
            }
            Name::StructFieldProj(str, fld) => format!("{}__get_{}", struct_to_string(str), fld),
            Name::StructDirectFieldName(str, fld) => format!("{}__{}", struct_to_string(str), fld),
            Name::StructGhostFieldProj(str, fld) => format!("{}__{}", struct_to_string(str), fld),
            Name::StructAuxFn(str, f) => format!("{}__aux_{}", struct_to_string(str), f),
            Name::StructContainerFn(str, fld) => {
                format!("{}__{}_container", struct_to_string(str), fld)
            }
            Name::StructContainerInv(str, fld) => {
                format!("{}__{}_container_inv", struct_to_string(str), fld)
            }
            Name::StructProjContainerInv(str, fld) => {
                format!("{}__{}_proj_container_inv", struct_to_string(str), fld)
            }
            Name::StructProjNull(str, fld) => {
                format!("{}__{}_proj_null", struct_to_string(str), fld)
            }
            Name::UnionFieldConstructor(u, fld) => {
                format!("Field_{}__{}", u, fld)
            }
            Name::UnionGhostFieldProj(u, fld) => format!("{}__{}", union_to_string(u), fld),
            Name::UnionFieldProj(u, fld) => format!("{}__get_{}", union_to_string(u), fld),
            Name::UnionAuxFn(u, f, fld) => format!("{}__aux_{}_{}", union_to_string(u), f, fld),
            Name::UnionActivateFn(u, fld) => {
                format!("{}__activate_{}", union_to_string(u), fld)
            }
            Name::TypeRefDefault(type_ref) => {
                format!("has_zero_default_{}", typeref_to_string(type_ref))
            }
        }
    }
}

const RESERVED: &[&str] = &[
    "fn", // keywords
    "assume",
    "requires",
    "ensures",
    "preserves",
    "continue",
    "break",
    "label",
    "goto",
    "return",
    "stt", // library names
    "stt_ghost",
    "stt_atomic",
    "ref",
    "array",
    "admit",
    "bool",
    "unit",
    "slprop",
    "emp",
    "emp_inames",
    "int",
    "nat",
    "not",
    "pulse_eager_unfold",
    "pulse_intro",
];

#[derive(Clone)]
struct NameMangling {
    map: HashMap<Name, Rc<str>>,
    used: HashSet<Rc<str>>,
}
impl NameMangling {
    fn new() -> Self {
        NameMangling {
            map: HashMap::new(),
            used: RESERVED.iter().map(|r| Rc::from(*r)).collect(),
        }
    }

    fn pick_new(&mut self, mut base: String) -> Rc<str> {
        if !self.used.contains(base.as_str()) {
            return Rc::from(base);
        }
        let base_init_len = base.len();
        for i in 1.. {
            base.truncate(base_init_len);
            write!(base, "_{}", i).unwrap();
            if !self.used.contains(base.as_str()) {
                return Rc::from(base);
            }
        }
        unreachable!()
    }

    fn mangle(&mut self, name: &Name) -> Rc<str> {
        if let Some(mangled) = self.map.get(name) {
            return mangled.clone();
        }

        let base = name.to_string();
        // Union field constructors must start uppercase (F* inductive requirement)
        let mangled = if matches!(name, Name::UnionFieldConstructor(..)) {
            self.pick_new(base)
        } else {
            self.pick_new(base.to_lowercase())
        };
        self.used.insert(mangled.clone());
        self.map.insert(name.clone(), mangled.clone());
        mangled
    }
}

struct ExBinding {
    name: Doc,
    ty: Doc,
}

/// Info about a single spec record field for a struct.
struct SpecFieldBinding {
    /// The spec record field name (e.g., "struct_simple__spec__y_0")
    field_name: Doc,
    /// The F* type of this spec field
    ty: Doc,
}

/// Controls how val bindings are generated during slprop emission.
enum ValNaming<'a> {
    /// Standard: standalone val names (val_x_0) stored in ExBinding list.
    /// Used for function signatures and old-style preds.
    Standard {
        quote: bool,
        bindings: &'a mut Vec<ExBinding>,
    },
    /// Spec record: val references become `spec_param.field_name`.
    /// Used for struct pred body with spec record parameter.
    SpecRecord {
        spec_param: &'a Doc,
        type_ref: &'a TypeRef,
        field_name: &'a Rc<IdentT>,
        bindings: &'a mut Vec<SpecFieldBinding>,
    },
}

/// Per-field spec info collected during struct pred analysis.
struct FieldSpecInfo {
    /// The struct field name (e.g., "y")
    field_ident: Rc<IdentT>,
    /// Spec bindings generated by this field (one per pointer dereference level)
    bindings: Vec<SpecFieldBinding>,
    /// SLProps for the Init predicate body
    init_props: Vec<Doc>,
}

#[derive(Clone, Copy)]
enum SLPropVariant<'a> {
    Init { perm: &'a Doc },
    Uninit,
}

struct Emitter<'a> {
    nm: NameMangling,
    diags: &'a mut Diagnostics,
    /// For each TypeRef, the types of the val params for Init/Uninit variants.
    type_val_params: HashMap<TypeRef, Vec<Doc>>,
    type_uninit_val_params: HashMap<TypeRef, Vec<Doc>>,
    /// When emitting a struct's pred, tracks the struct name to avoid
    /// infinite recursion on self-referential pointer fields.
    defining_struct: Option<Rc<str>>,
    /// The module currently being emitted (for qualified name resolution).
    current_module: String,
    /// Maps function/let/global/opaque identifiers to their owning module.
    fn_module_map: HashMap<Rc<str>, String>,
    /// Maps typedef names that are OpaqueTypeDecls to their Type_* module (overrides Typedef_*).
    typedef_override_map: HashMap<Rc<str>, String>,
    /// Whether the function body currently being emitted is `_total`. Set at body
    /// entry in `emit_fn_defn`; read by the `FnPtrCall` arm to emit `call` (total
    /// body) vs `call_div` (divergent body).
    current_fn_total: bool,
    tmp_counter: usize,
}

impl<'a> Emitter<'a> {
    fn report(&mut self, msg: String, loc: &SourceInfo) {
        self.diags.report(Diagnostic {
            loc: loc.location().clone(),
            level: DiagnosticLevel::Error,
            msg,
        });
    }

    fn fresh_tmp(&mut self, prefix: &str) -> Doc {
        let tmp = Doc::text(format!("__pal_{}_{}", prefix, self.tmp_counter));
        self.tmp_counter += 1;
        tmp
    }

    /// Emit a Name with full module qualification when it refers to a different module.
    fn emit_name(&mut self, name: Name) -> Doc {
        let mangled = self.nm.mangle(&name).to_string();
        // For Name::Fn, look up the actual module from the declaration-based map
        let owner_module = if let Name::Fn(ref v) = name {
            self.fn_module_map.get(v).cloned()
        } else {
            // Check typedef_override_map for TypeRef::Typedef names (OpaqueTypeDecl)
            let base_module = module_for_name(&name);
            match &name {
                Name::TypeRef(TypeRef::Typedef(t))
                | Name::TypeRefPred(TypeRef::Typedef(t))
                | Name::TypeRefUninitPred(TypeRef::Typedef(t))
                | Name::TypeRefDefault(TypeRef::Typedef(t)) => {
                    self.typedef_override_map.get(t).cloned().or(base_module)
                }
                _ => base_module,
            }
        };
        if let Some(owner_module) = owner_module {
            if owner_module == self.current_module {
                Doc::text(mangled)
            } else {
                Doc::text(format!("{}.{}", owner_module, mangled))
            }
        } else {
            Doc::text(mangled)
        }
    }
}

fn extract_base_ident(this: &Rc<Expr>) -> Rc<IdentT> {
    match &this.val {
        ExprT::Var(x) => x.val.clone(),
        ExprT::Deref(inner) => extract_base_ident(inner),
        ExprT::Member(_, field) => field.val.clone(),
        _ => Rc::from("v"),
    }
}

fn wrap_exists(bindings: &[ExBinding], props: Vec<Doc>) -> Doc {
    let star = mk_star(props);
    if bindings.is_empty() {
        return star;
    }
    let binding_docs = Doc::concat(bindings.iter().map(|b| {
        Doc::line().append(parens(
            b.name
                .clone()
                .append(":")
                .append(Doc::line())
                .append(b.ty.clone()),
        ))
    }));
    Doc::text("exists*")
        .append(binding_docs)
        .append(Doc::text("."))
        .group()
        .append(Doc::line())
        .append(star)
}

/// The `ARG` domain of a function pointer given its (already-emitted) argument
/// type docs: `unit` for arity 0, the single type for arity 1, and a right-
/// nested tuple `(a & b & ..)` for arity >= 2.
fn fnptr_domain_doc(arg_docs: Vec<Doc>) -> Doc {
    match arg_docs.len() {
        0 => Doc::text("unit"),
        1 => arg_docs.into_iter().next().unwrap(),
        _ => parens(Doc::intersperse(arg_docs, Doc::text(" & "))),
    }
}

/// Visit every sub-expression of `e`, outermost first.
fn walk_expr_tree(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match &e.val {
        // Leaves.
        ExprT::Var(_)
        | ExprT::BoolLit(_)
        | ExprT::IntLit(_, _)
        | ExprT::FloatLit(_, _)
        | ExprT::FnRef(_)
        | ExprT::InlinePulse(_, _)
        | ExprT::Malloc(_)
        | ExprT::Calloc(_)
        | ExprT::SizeOf(_)
        | ExprT::AlignOf(_)
        | ExprT::Error(_) => {}
        // One sub-expression.
        ExprT::Deref(a)
        | ExprT::Member(a, _)
        | ExprT::VAttr(_, a)
        | ExprT::Ref(a)
        | ExprT::UnOp(_, a)
        | ExprT::Cast(a, _)
        | ExprT::ContainerOf(a, _, _)
        | ExprT::Live(a)
        | ExprT::Old(a)
        | ExprT::Forall(_, _, a)
        | ExprT::Exists(_, _, a)
        | ExprT::UnionInit(_, _, a)
        | ExprT::MallocArray(_, a)
        | ExprT::CallocArray(_, a)
        | ExprT::MallocFlex(_, a)
        | ExprT::CallocFlex(_, a)
        | ExprT::MemsetZero(_, a)
        | ExprT::Free(a)
        | ExprT::PreIncr(a)
        | ExprT::PostIncr(a)
        | ExprT::PreDecr(a)
        | ExprT::PostDecr(a) => walk_expr_tree(a, f),
        // Two sub-expressions.
        ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
            walk_expr_tree(a, f);
            walk_expr_tree(b, f);
        }
        // Three sub-expressions.
        ExprT::Cond(a, b, c) | ExprT::Memset(_, a, b, c) => {
            walk_expr_tree(a, f);
            walk_expr_tree(b, f);
            walk_expr_tree(c, f);
        }
        // Sequences.
        ExprT::FnCall(_, args) => args.iter().for_each(|a| walk_expr_tree(a, f)),
        ExprT::FnPtrCall(callee, args) => {
            walk_expr_tree(callee, f);
            args.iter().for_each(|a| walk_expr_tree(a, f));
        }
        ExprT::StructInit(_, fields) => fields.iter().for_each(|(_, a)| walk_expr_tree(a, f)),
        ExprT::ArrayInit { elems, .. } => elems.iter().for_each(|a| walk_expr_tree(a, f)),
    }
}

/// Visit every sub-expression appearing in `s`, including nested statements.
fn walk_stmt_tree(s: &Stmt, f: &mut impl FnMut(&Expr)) {
    match &s.val {
        StmtT::Decl(_, _)
        | StmtT::Break
        | StmtT::Continue
        | StmtT::Return(None)
        | StmtT::GhostStmt(_)
        | StmtT::Goto(_)
        | StmtT::Label { .. }
        | StmtT::Error => {}
        StmtT::Call(e)
        | StmtT::Assert(e)
        | StmtT::Return(Some(e))
        | StmtT::Let(_, _, e)
        | StmtT::DeclStackArray { size: e, .. } => walk_expr_tree(e, f),
        StmtT::Assign(l, r) => {
            walk_expr_tree(l, f);
            walk_expr_tree(r, f);
        }
        StmtT::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            walk_expr_tree(cond, f);
            then_branch.iter().for_each(|s| walk_stmt_tree(s, f));
            else_branch.iter().for_each(|s| walk_stmt_tree(s, f));
        }
        StmtT::Match {
            scrutinee,
            branches,
            default_branch,
            ..
        } => {
            walk_expr_tree(scrutinee, f);
            branches
                .iter()
                .for_each(|b| b.body.iter().for_each(|s| walk_stmt_tree(s, f)));
            default_branch.iter().for_each(|s| walk_stmt_tree(s, f));
        }
        StmtT::While { cond, body, .. } => {
            walk_expr_tree(cond, f);
            body.iter().for_each(|s| walk_stmt_tree(s, f));
        }
        StmtT::GotoBlock { body, .. } => body.iter().for_each(|s| walk_stmt_tree(s, f)),
    }
}

/// Collect the set of C functions whose address is taken anywhere in the
/// translation unit (`&f` or bare `f` decaying to a function pointer, both
/// modeled as `ExprT::FnRef`). Each such function needs its fnptr wrapper
/// (`func_<f>__fp`) emitted in its module.
///
/// The `Decl`-level match below is exhaustive with no `_` catch-all on
/// purpose: a missed variant silently emits a reference to a `Funcptr_<f>`
/// that never gets written, surfacing only as F* `Error 72` and never as a
/// PAL diagnostic.
fn collect_addr_taken(decls: &[Decl]) -> HashSet<Rc<str>> {
    let mut set = HashSet::new();
    let mut note = |e: &Expr| {
        if let ExprT::FnRef(f) = &e.val {
            set.insert(f.val.clone());
        }
    };
    for decl in decls {
        match &decl.val {
            DeclT::FnDefn(fd) => fd.body.iter().for_each(|s| walk_stmt_tree(s, &mut note)),
            // A global initializer can mention a function too, e.g.
            // `_pure ops g_ops = { .op = add };`.
            DeclT::GlobalVar(gv) => {
                if let Some(init) = &gv.init {
                    walk_expr_tree(init, &mut note)
                }
            }
            DeclT::LetDecl(ld) => walk_expr_tree(&ld.body, &mut note),
            DeclT::FnDecl(_)
            | DeclT::Typedef(_)
            | DeclT::StructDefn(_)
            | DeclT::StructDecl(_)
            | DeclT::UnionDefn(_)
            | DeclT::IncludeDecl(_)
            | DeclT::OpaqueTypeDecl(_) => {}
        }
    }
    set
}

impl<'a> Emitter<'a> {
    fn emit_type(&mut self, env: &Env, ty: &Type) -> Doc {
        annotated(ty, || {
            match &ty.val {
                TypeT::Void => Doc::text("unit"),

                // TODO: support all widths
                TypeT::Int {
                    signed: false,
                    width,
                } => Doc::text(format!("UInt{}.t", width)),
                TypeT::Int {
                    signed: true,
                    width,
                } => Doc::text(format!("Int{}.t", width)),
                TypeT::Float { width: 32 } => Doc::text("Pulse.Lib.C.float32"),
                TypeT::Float { width: 64 } => Doc::text("Pulse.Lib.C.float64"),
                TypeT::Float { width } => {
                    self.report(
                        format!("unsupported floating-point width {}", width),
                        &ty.loc,
                    );
                    Doc::text("unit")
                }

                TypeT::Bool => Doc::text("bool"),
                TypeT::SizeT => Doc::text("SizeT.t"),
                TypeT::PtrdiffT => Doc::text("Pulse.Lib.C.PtrdiffT.t"),

                TypeT::Pointer(to, PointerKind::Array | PointerKind::ArrayPtr) => {
                    unaryfn(Doc::text("array"), self.emit_type(env, to))
                }
                TypeT::Pointer(to, PointerKind::Ref | PointerKind::Unknown) => {
                    unaryfn(Doc::text("ref"), self.emit_type(env, to))
                }
                // A `core_ref` is a non-parametric raw pointer: drop the pointee
                // type entirely so the emitted type carries no dependency on it
                // (this is what breaks the module/type cycle for recursive structs).
                TypeT::Pointer(_, PointerKind::Core) => Doc::text("core_ref"),
                TypeT::FixedArray(elem_ty, len) => naryfn([
                    Doc::text("full_array_lspec"),
                    self.emit_type(env, elem_ty),
                    Doc::text(len.to_string()),
                ]),
                // A flexible array member is modelled like a fixed inline array
                // but without a statically known length, so it lacks the length
                // pin of `full_array_lspec`. Any length relation to a sibling
                // field is expressed as a `pure` fact in the struct predicate.
                TypeT::FlexArray(elem_ty) => {
                    unaryfn(Doc::text("full_array_spec"), self.emit_type(env, elem_ty))
                }
                TypeT::Unknown => Doc::text("unit"),
                TypeT::Error => Doc::text("unit"),

                TypeT::FnPtr { args, ret, .. } => {
                    let domain = self.fnptr_domain(env, args);
                    let range = self.emit_type(env, ret);
                    naryfn([Doc::text("Pulse.Lib.C.FuncPtr.func_ptr"), domain, range])
                }

                TypeT::TypeRef(n) => self.emit_name(Name::TypeRef(n.into())),

                TypeT::SLProp => Doc::text("slprop"),
                TypeT::SpecInt => Doc::text("int"),
                TypeT::SpecNat => Doc::text("nat"),

                TypeT::Refine(ty, _)
                | TypeT::RefineAlways(ty, _)
                | TypeT::RefineUninit(ty, _)
                | TypeT::RefineValue(ty, ..)
                | TypeT::Plain(ty)
                | TypeT::Nullable(ty) => self.emit_type(env, ty),
            }
        })
    }

    /// Emit the zero-default value for a C type (corresponding to the zero bitpattern).
    fn emit_type_default(&mut self, env: &Env, ty: &Type) -> Doc {
        match &ty.val {
            TypeT::Int { signed, width } => {
                let (modu, ctor) = if *signed {
                    (format!("Int{}", width), "int_to_t")
                } else {
                    (format!("UInt{}", width), "uint_to_t")
                };
                parens(Doc::text(format!("{}.{} 0", modu, ctor)))
            }
            TypeT::Float { width: 32 } => Doc::text("Pulse.Lib.C.float32_zero"),
            TypeT::Float { width: 64 } => Doc::text("Pulse.Lib.C.float64_zero"),
            TypeT::Bool => Doc::text("false"),
            TypeT::SizeT => Doc::text("0sz"),
            TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown) => Doc::text("null"),
            TypeT::Pointer(_, PointerKind::Core) => Doc::text("core_null"),
            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr) => {
                Doc::text("zero_default")
            }
            TypeT::FixedArray(elem_ty, length) => parens(naryfn([
                Doc::text("array_spec_zeroed"),
                self.emit_type(env, elem_ty),
                parens(Doc::text(format!("SizeT.v {}sz", length))),
                self.emit_type_default(env, elem_ty),
            ])),
            // Zero-length flexible array member default (a `full_array_spec` of
            // length 0), satisfying any `array_spec_len == 0` relation to a
            // zeroed sibling length field.
            TypeT::FlexArray(elem_ty) => parens(naryfn([
                Doc::text("array_spec_zeroed"),
                self.emit_type(env, elem_ty),
                Doc::text("0"),
                self.emit_type_default(env, elem_ty),
            ])),
            TypeT::Void => Doc::text("()"),
            TypeT::TypeRef(_) => Doc::text("zero_default"),
            // A function pointer's zero bitpattern is the null function pointer
            // (`has_zero_default_func_ptr` in the library). Uses the same
            // `func_ptr domain range` shaping as `emit_type`.
            TypeT::FnPtr { args, ret, .. } => {
                let domain = self.fnptr_domain(env, args);
                let range = self.emit_type(env, ret);
                naryfn([Doc::text("Pulse.Lib.C.FuncPtr.null"), domain, range])
            }
            TypeT::Refine(ty, _)
            | TypeT::RefineAlways(ty, _)
            | TypeT::RefineUninit(ty, _)
            | TypeT::RefineValue(ty, ..)
            | TypeT::Plain(ty)
            | TypeT::Nullable(ty) => self.emit_type_default(env, ty),
            _ => {
                self.report(format!("no zero default for type {}", ty), &ty.loc);
                Doc::text("(admit())")
            }
        }
    }

    /// Emit the zero-default value for a struct/union field. For
    /// `Plain` fields this is just the type's zero default.
    fn emit_field_default(&mut self, env: &Env, field: &Field) -> Doc {
        match &field.val {
            FieldT::Plain { ty, .. } => self.emit_type_default(env, ty),
            // A bit-field's record cell has the refined machine type, so its
            // default must be a concrete machine zero (e.g. `UInt16.uint_to_t 0`,
            // `0` for width `N >= 1`) that visibly satisfies the `< pow2 N`
            // refinement — not the generic `zero_default`, which has no instance
            // for the refined type. Resolve typedefs to reach the machine int.
            FieldT::BitField { ty, .. } => {
                self.emit_type_default(env, &env.vtype_whnf(ty.clone().into()))
            }
        }
    }

    /// Emit the range-refined machine type backing an unsigned bit-field of the
    /// given declared underlying integer type and bit-width:
    /// `(v:UIntW.t{UIntW.v v < pow2 N})`. The declared type may be a typedef
    /// (e.g. `uint16_t`), so it is resolved to weak-head normal form to find the
    /// underlying machine width for the `UIntW.v` projection in the refinement.
    fn emit_bitfield_value_type(&mut self, env: &Env, ty: &Type, width: u32) -> Doc {
        let base = self.emit_type(env, ty);
        let modu = match &env.vtype_whnf(ty.clone().into()).val {
            TypeT::Int {
                signed: false,
                width: w,
            } => get_int_mod(&false, w),
            _ => None,
        };
        match modu {
            Some(m) => parens(
                Doc::text("v:")
                    .append(Doc::line())
                    .append(base)
                    .append(Doc::line())
                    .append(Doc::text(format!("{{{}.v v < pow2 {}}}", m, width))),
            ),
            // Should not happen for a well-formed unsigned bit-field; fall back
            // to the unrefined machine type.
            None => base,
        }
    }

    /// If `lhs` is a struct member access (`s->f` / `s.f`) whose field is an
    /// unsigned bit-field, return its bit-width and the fully-qualified masking
    /// helper (`Pulse.Lib.C.BitField.mask_uW`) for its underlying machine width.
    /// A write to a bit-field stores `mask_uW width rhs` so the masked value
    /// satisfies the cell's `< pow2 width` refinement (C unsigned truncation).
    fn bitfield_member_mask(&self, env: &Env, lhs: &Expr) -> Option<(u32, &'static str)> {
        let ExprT::Member(base, fld) = &lhs.val else {
            return None;
        };
        let base_ty = env.vtype_whnf(env.infer_expr(base).ok()?);
        let struct_name = match &base_ty.val {
            TypeT::TypeRef(TypeRefKind::Struct(s)) => s.clone(),
            _ => return None,
        };
        let sdef = env.lookup_struct(&struct_name)?;
        let field = sdef.fields.iter().find(|f| f.val.name().val == fld.val)?;
        let width = field.val.bit_width()?;
        let underlying = env.vtype_whnf(field.val.logical_type(&field.loc).into());
        let mask_fn = match &underlying.val {
            TypeT::Int {
                signed: false,
                width: mw,
            } => get_bitfield_mask_fn(mw)?,
            _ => return None,
        };
        Some((width, mask_fn))
    }

    /// Render the F* type appearing in a struct/union's noeq record for
    /// `field`. For `Plain` fields this is the stored type
    fn emit_field_record_type(&mut self, env: &Env, field: &Field) -> Doc {
        match &field.val {
            FieldT::Plain { name: _, ty } => self.emit_type(env, ty),
            FieldT::BitField { ty, width, .. } => self.emit_bitfield_value_type(env, ty, *width),
        }
    }

    /// Render the type of an inline-array ghost projection — the array
    /// *handle* itself (no `ref` wrapper), refined to the same static
    /// length as the noeq contents. Panics if called on a non-array field.
    fn emit_field_array_handle_type(&mut self, env: &Env, field: &Field) -> Doc {
        // Flexible array members have no statically known length, so their
        // handle type carries no `{ length a == N }` pin. Without a refinement
        // there is no need for the `a:` binder either (and F* warns about the
        // unused binder), so emit the bare `array` handle type.
        if let Some((elem_ty, _)) = field.val.flex_array_info() {
            return unaryfn(Doc::text("array"), self.emit_type(env, elem_ty));
        }
        let (elem_ty, length) = field
            .val
            .fixed_array_info()
            .expect("emit_field_array_handle_type called on non-array field");
        parens(
            Doc::text("a:")
                .append(Doc::line())
                .append(unaryfn(Doc::text("array"), self.emit_type(env, elem_ty)))
                .append(Doc::line())
                .append(Doc::text(format!("{{ length a == {} }}", length))),
        )
    }

    /// Render the F* type of the ghost projection / getter for `field`.
    /// For inline-array fields this is the bare refined array handle
    /// (no `ref` wrapper); for plain fields it is `ref T`.
    fn emit_field_projection_type(&mut self, env: &Env, field: &Field) -> Doc {
        if field.val.is_array() {
            self.emit_field_array_handle_type(env, field)
        } else {
            match &field.val {
                FieldT::Plain { name: _, ty } => unaryfn(Doc::text("ref"), self.emit_type(env, ty)),
                FieldT::BitField { ty, width, .. } => unaryfn(
                    Doc::text("ref"),
                    self.emit_bitfield_value_type(env, ty, *width),
                ),
            }
        }
    }

    fn subst_this_rvalue(&mut self, env: &Env, rvalue: &mut Expr, this: &Rc<Expr>) {
        match &mut rvalue.val {
            ExprT::Var(x) => {
                if &*x.val == "this" {
                    *rvalue = (**this).clone()
                }
            }
            ExprT::Deref(rv) => self.subst_this_rvalue(env, Rc::make_mut(rv), this),
            ExprT::Member(x, _a) => self.subst_this_rvalue(env, Rc::make_mut(x), this),
            ExprT::BoolLit(_) => {}
            ExprT::IntLit(..) => {}
            ExprT::FloatLit(..) => {}
            ExprT::Ref(lv) => self.subst_this_rvalue(env, Rc::make_mut(lv), this),
            ExprT::UnOp(_, arg) => {
                self.subst_this_rvalue(env, Rc::make_mut(arg), this);
            }
            ExprT::BinOp(_, lhs, rhs) => {
                self.subst_this_rvalue(env, Rc::make_mut(lhs), this);
                self.subst_this_rvalue(env, Rc::make_mut(rhs), this);
            }
            ExprT::FnCall(_f, args) => {
                for arg in args {
                    self.subst_this_rvalue(env, Rc::make_mut(arg), this);
                }
            }
            ExprT::FnRef(_) => {}
            ExprT::FnPtrCall(f, args) => {
                self.subst_this_rvalue(env, Rc::make_mut(f), this);
                for arg in args {
                    self.subst_this_rvalue(env, Rc::make_mut(arg), this);
                }
            }
            ExprT::Cast(val, _) => {
                self.subst_this_rvalue(env, Rc::make_mut(val), this);
            }
            ExprT::InlinePulse(val, _) => {
                self.subst_inline_pulse_code_this(env, Rc::make_mut(val), this)
            }
            ExprT::Error(_ty) => {}
            ExprT::Live(val) => self.subst_this_rvalue(env, Rc::make_mut(val), this),
            ExprT::Old(val) => self.subst_this_rvalue(env, Rc::make_mut(val), this),
            ExprT::Forall(_, _, body) | ExprT::Exists(_, _, body) => {
                self.subst_this_rvalue(env, Rc::make_mut(body), this);
            }
            ExprT::StructInit(_, fields) => {
                for (_fld, val) in fields {
                    self.subst_this_rvalue(env, Rc::make_mut(val), this);
                }
            }
            ExprT::UnionInit(_, _, val) => {
                self.subst_this_rvalue(env, Rc::make_mut(val), this);
            }
            ExprT::ArrayInit { elems, .. } => {
                for elem in elems {
                    self.subst_this_rvalue(env, Rc::make_mut(elem), this);
                }
            }
            ExprT::Malloc(_) | ExprT::Calloc(_) => {}
            ExprT::MallocArray(_, count) | ExprT::CallocArray(_, count) => {
                self.subst_this_rvalue(env, Rc::make_mut(count), this);
            }
            ExprT::MallocFlex(_, count) | ExprT::CallocFlex(_, count) => {
                self.subst_this_rvalue(env, Rc::make_mut(count), this);
            }
            ExprT::Memset(_, ptr, value, count) => {
                self.subst_this_rvalue(env, Rc::make_mut(ptr), this);
                self.subst_this_rvalue(env, Rc::make_mut(value), this);
                self.subst_this_rvalue(env, Rc::make_mut(count), this);
            }
            ExprT::MemsetZero(_, ptr) => {
                self.subst_this_rvalue(env, Rc::make_mut(ptr), this);
            }
            ExprT::Free(val) => self.subst_this_rvalue(env, Rc::make_mut(val), this),
            ExprT::ContainerOf(ptr, _, _) => self.subst_this_rvalue(env, Rc::make_mut(ptr), this),
            ExprT::PreIncr(val)
            | ExprT::PostIncr(val)
            | ExprT::PreDecr(val)
            | ExprT::PostDecr(val) => self.subst_this_rvalue(env, Rc::make_mut(val), this),
            ExprT::VAttr(_, x) => self.subst_this_rvalue(env, Rc::make_mut(x), this),
            ExprT::Index(arr, idx) => {
                self.subst_this_rvalue(env, Rc::make_mut(arr), this);
                self.subst_this_rvalue(env, Rc::make_mut(idx), this);
            }
            ExprT::Cond(cond, then_expr, else_expr) => {
                self.subst_this_rvalue(env, Rc::make_mut(cond), this);
                self.subst_this_rvalue(env, Rc::make_mut(then_expr), this);
                self.subst_this_rvalue(env, Rc::make_mut(else_expr), this);
            }
            ExprT::AssignExpr(lhs, rhs) => {
                self.subst_this_rvalue(env, Rc::make_mut(lhs), this);
                self.subst_this_rvalue(env, Rc::make_mut(rhs), this);
            }
            ExprT::SizeOf(_) | ExprT::AlignOf(_) => {}
        }
    }

    fn subst_inline_pulse_code_this(
        &mut self,
        env: &Env,
        val: &mut InlinePulseCode,
        this: &Rc<Expr>,
    ) {
        for tok in &mut val.tokens {
            match tok {
                InlinePulseToken::Verbatim(_)
                | InlinePulseToken::TypeAntiquot { .. }
                | InlinePulseToken::FieldAntiquot { .. }
                | InlinePulseToken::AuxFnAntiquot { .. }
                | InlinePulseToken::Declare { .. } => {}
                InlinePulseToken::RValueAntiquot { expr, .. }
                | InlinePulseToken::LValueAntiquot { expr, .. } => {
                    self.subst_this_rvalue(env, Rc::make_mut(expr), this);
                }
            }
        }
    }

    fn emit_inline_pulse_tokens(&mut self, env: &mut Env, code: &InlinePulseCode) -> Doc {
        Doc::concat(code.tokens.iter().map(|tok| {
            match tok {
                InlinePulseToken::Verbatim(ct) => Doc::text(ct.before)
                    .append(annotated(&ct.text, || Doc::text(ct.text.val.to_string()))),
                InlinePulseToken::RValueAntiquot { before, expr } => {
                    Doc::text(*before).append(self.emit_rvalue(env, expr))
                }
                InlinePulseToken::LValueAntiquot { before, expr } => {
                    Doc::text(*before).append(self.emit_expr(env, expr).into_doc())
                }
                InlinePulseToken::TypeAntiquot { before, ty } => {
                    Doc::text(*before).append(self.emit_type(env, ty))
                }
                InlinePulseToken::FieldAntiquot {
                    before,
                    ty,
                    field_name,
                } => {
                    let resolved = env.vtype_whnf(ty.clone().into());
                    match &resolved.val {
                        TypeT::TypeRef(TypeRefKind::Struct(struct_name)) => Doc::text(*before)
                            .append(self.emit_name(Name::StructDirectFieldName(
                                struct_name.val.clone(),
                                field_name.val.clone(),
                            ))),
                        TypeT::TypeRef(TypeRefKind::Union(union_name)) => Doc::text(*before)
                            .append(self.emit_name(Name::UnionFieldConstructor(
                                union_name.val.clone(),
                                field_name.val.clone(),
                            ))),
                        _ => {
                            self.report(
                                format!("$field: expected struct or union type, got {}", ty),
                                &ty.loc,
                            );
                            Doc::text(*before).append("(* $field: not a struct or union type *)")
                        }
                    }
                }
                InlinePulseToken::AuxFnAntiquot {
                    before,
                    ty,
                    field_name,
                    kind,
                } => {
                    let resolved = env.vtype_whnf(ty.clone().into());
                    match &resolved.val {
                        TypeT::TypeRef(TypeRefKind::Struct(struct_name)) => {
                            match kind.struct_aux_name() {
                                None => {
                                    self.report(
                                        format!("${}: not supported for struct types", kind.keyword()),
                                        &ty.loc,
                                    );
                                    Doc::text(*before).append(format!("(* ${}: not supported for structs *)", kind.keyword()))
                                }
                                Some(aux_name) => {
                                    if field_name.is_some() {
                                        self.report(
                                            format!("${}: struct type does not take a field name", kind.keyword()),
                                            &ty.loc,
                                        );
                                    }
                                    Doc::text(*before).append(self.emit_name(Name::StructAuxFn(
                                        struct_name.val.clone(),
                                        aux_name.into(),
                                    )))
                                }
                            }
                        }
                        TypeT::TypeRef(TypeRefKind::Union(union_name)) => {
                            if matches!(kind, AuxFnKind::Activate) {
                                match field_name {
                                    Some(fld) => Doc::text(*before).append(self.emit_name(
                                        Name::UnionActivateFn(
                                            union_name.val.clone(),
                                            fld.val.clone(),
                                        ),
                                    )),
                                    None => {
                                        self.report(
                                            "$activate: union type requires an arm name (use type::arm syntax)".to_string(),
                                            &ty.loc,
                                        );
                                        Doc::text(*before).append("(* $activate: missing arm name *)")
                                    }
                                }
                            } else {
                            match (kind.union_aux_name(), field_name) {
                                (Some(aux_name), Some(fld)) => {
                                    Doc::text(*before).append(self.emit_name(Name::UnionAuxFn(
                                        union_name.val.clone(),
                                        aux_name,
                                        fld.val.clone(),
                                    )))
                                }
                                (None, _) => {
                                    self.report(
                                        format!("${}: not supported for union types", kind.keyword()),
                                        &ty.loc,
                                    );
                                    Doc::text(*before).append(format!("(* ${}: not supported for unions *)", kind.keyword()))
                                }
                                (_, None) => {
                                    self.report(
                                        format!("${}: union type requires a field name (use type::field syntax)", kind.keyword()),
                                        &ty.loc,
                                    );
                                    Doc::text(*before).append(format!("(* ${}: missing field name *)", kind.keyword()))
                                }
                            }
                            }
                        }
                        _ => {
                            self.report(
                                format!("${}: expected struct or union type, got {}", kind.keyword(), ty),
                                &ty.loc,
                            );
                            Doc::text(*before).append(format!("(* ${}: not a struct or union type *)", kind.keyword()))
                        }
                    }
                }
                InlinePulseToken::Declare { ident, ty } => {
                    env.push_var_decl(ident, ty.clone(), LocalDeclKind::RValue);
                    Doc::nil()
                }
            }
        }))
    }

    /// Push a val binding using the naming strategy, with an auto-generated name based on `this`.
    /// Returns the Doc to use as the val reference in the slprop.
    fn push_val_binding(&mut self, naming: &mut ValNaming, this: &Rc<Expr>, ty: Doc) -> Doc {
        match naming {
            ValNaming::Standard { quote, bindings } => {
                let idx = bindings.len() as u32;
                let raw = Doc::text(
                    self.nm
                        .mangle(&Name::Val(extract_base_ident(this), idx))
                        .to_string(),
                );
                let val_name = if *quote {
                    Doc::text("'").append(raw)
                } else {
                    raw
                };
                bindings.push(ExBinding {
                    name: val_name.clone(),
                    ty,
                });
                val_name
            }
            ValNaming::SpecRecord {
                spec_param,
                type_ref,
                field_name,
                bindings,
            } => {
                let idx = bindings.len() as u32;
                let spec_field_name_str = format!("{}_{}", field_name, idx);
                let spec_field_name = Doc::text(
                    self.nm
                        .mangle(&Name::TypeRefSpecField(
                            (*type_ref).clone(),
                            spec_field_name_str,
                        ))
                        .to_string(),
                );
                let val_access = spec_param
                    .clone()
                    .append(".")
                    .append(spec_field_name.clone());
                bindings.push(SpecFieldBinding {
                    field_name: spec_field_name,
                    ty,
                });
                val_access
            }
        }
    }

    /// Push a val binding with an explicit name (used by RefineValue).
    /// Returns the Doc to use as the val reference in the slprop.
    fn push_val_binding_explicit(&mut self, naming: &mut ValNaming, raw_name: Doc, ty: Doc) -> Doc {
        match naming {
            ValNaming::Standard { quote, bindings } => {
                let val_name = if *quote {
                    Doc::text("'").append(raw_name)
                } else {
                    raw_name
                };
                bindings.push(ExBinding {
                    name: val_name.clone(),
                    ty,
                });
                val_name
            }
            ValNaming::SpecRecord {
                spec_param,
                type_ref,
                bindings,
                ..
            } => {
                // For explicit names in spec context, use the name as the field name
                let spec_field_name = Doc::text(
                    self.nm
                        .mangle(&Name::TypeRefSpecField(
                            (*type_ref).clone(),
                            format!("{}", raw_name.pretty(80)),
                        ))
                        .to_string(),
                );
                let val_access = spec_param
                    .clone()
                    .append(".")
                    .append(spec_field_name.clone());
                bindings.push(SpecFieldBinding {
                    field_name: spec_field_name,
                    ty,
                });
                val_access
            }
        }
    }

    fn emit_type_slprop(
        &mut self,
        env: &Env,
        ty: &Type,
        variant: SLPropVariant,
        naming: &mut ValNaming,
        props: &mut Vec<Doc>,
        this: &Rc<Expr>,
    ) {
        self.emit_type_slprop_inner(env, ty, variant, naming, props, this, None);
    }

    fn emit_type_slprop_inner(
        &mut self,
        env: &Env,
        ty: &Type,
        variant: SLPropVariant,
        naming: &mut ValNaming,
        props: &mut Vec<Doc>,
        this: &Rc<Expr>,
        resolving_struct: Option<&str>,
    ) {
        match &ty.val {
            TypeT::Void
            | TypeT::Bool
            | TypeT::Int { .. }
            | TypeT::Float { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::SpecInt
            | TypeT::SpecNat
            | TypeT::SLProp
            | TypeT::FixedArray(_, _)
            | TypeT::FlexArray(_)
            | TypeT::FnPtr { .. }
            | TypeT::Unknown => {}
            TypeT::Pointer(pointee_ty, kind) => {
                let this_doc = self.emit_rvalue(env, this);
                match kind {
                    PointerKind::Ref | PointerKind::Unknown => match variant {
                        SLPropVariant::Init { perm } => {
                            let pointee_type_doc = self.emit_type(env, pointee_ty);
                            let val_name = self.push_val_binding(naming, this, pointee_type_doc);
                            let slprop = annotated(ty, || {
                                naryfn([
                                    Doc::text("Pulse.Lib.Reference.pts_to"),
                                    this_doc,
                                    Doc::text("#").append(perm.clone()),
                                    val_name,
                                ])
                            });
                            props.push(slprop);
                            // Skip recursion for self-referential struct pointers
                            let is_self_ref = match &pointee_ty.val {
                                TypeT::TypeRef(TypeRefKind::Struct(s)) => {
                                    self.defining_struct.as_deref() == Some(&*s.val)
                                }
                                _ => false,
                            };
                            if !is_self_ref {
                                let derefed = ExprT::Deref(this.clone()).with_loc(this.loc.clone());
                                self.emit_type_slprop_inner(
                                    env,
                                    pointee_ty,
                                    variant,
                                    naming,
                                    props,
                                    &derefed,
                                    resolving_struct,
                                );
                            }
                        }
                        SLPropVariant::Uninit => {
                            props.push(annotated(ty, || {
                                unaryfn(Doc::text("Pulse.Lib.Reference.pts_to_uninit"), this_doc)
                            }));
                        }
                    },
                    PointerKind::Array => {
                        let pointee_type_doc = self.emit_type(env, pointee_ty);
                        let val_type_doc = match variant {
                            SLPropVariant::Init { .. } => {
                                unaryfn(Doc::text("full_array_spec"), pointee_type_doc)
                            }
                            SLPropVariant::Uninit => {
                                // Uninitialized arrays don't satisfy `initialized`
                                // so we must use `array_spec` (not `full_array_spec`).
                                // `array_pts_to_uninit` adds the `full_mask` constraint.
                                unaryfn(Doc::text("array_spec"), pointee_type_doc)
                            }
                        };
                        let val_name = self.push_val_binding(naming, this, val_type_doc);
                        match variant {
                            SLPropVariant::Init { perm } => props.push(annotated(ty, || {
                                naryfn([
                                    Doc::text("array_pts_to_full"),
                                    this_doc,
                                    perm.clone(),
                                    val_name,
                                ])
                            })),
                            SLPropVariant::Uninit => props.push(annotated(ty, || {
                                naryfn([Doc::text("array_pts_to_uninit"), this_doc, val_name])
                            })),
                        }
                    }
                    PointerKind::ArrayPtr => {
                        // ArrayPtr has no data ownership — arrayptr_pts_to is
                        // expressed by the user via _slprop/_inline_pulse for MVP
                    }
                    PointerKind::Core => {
                        // A `core_ref` carries no automatic ownership: the user
                        // supplies the (recursive) ownership predicate by hand via
                        // _include_pulse, recovering a typed `ref` with
                        // `core_to_ref`. This is what breaks predicate recursion
                        // for (mutually) recursive structs.
                    }
                }
            }
            TypeT::TypeRef(n) => {
                if let TypeRefKind::Struct(name) = n {
                    if resolving_struct != Some(&name.val) {
                        if let Some(decl) = env.lookup_struct(name) {
                            // Record attributes are parsed once on StructDefn.
                            // Bypass lookup for the cached tree's inner self
                            // reference so it emits the raw named predicate.
                            return self.emit_type_slprop_inner(
                                env,
                                &decl.refines,
                                variant,
                                naming,
                                props,
                                this,
                                Some(&name.val),
                            );
                        }
                    }
                }
                let this_doc = self.emit_rvalue(env, this);
                let (val_param_types, pred_name) = match variant {
                    SLPropVariant::Init { .. } => (
                        self.type_val_params
                            .get(&TypeRef::from(n))
                            .cloned()
                            .unwrap_or_default(),
                        self.emit_name(Name::TypeRefPred(n.into())),
                    ),
                    SLPropVariant::Uninit => (
                        self.type_uninit_val_params
                            .get(&TypeRef::from(n))
                            .cloned()
                            .unwrap_or_default(),
                        self.emit_name(Name::TypeRefUninitPred(n.into())),
                    ),
                };
                let mut val_args: Vec<Doc> = vec![];
                for vp_type in &val_param_types {
                    let val_name = self.push_val_binding(naming, this, vp_type.clone());
                    val_args.push(val_name);
                }
                let mut args: Vec<Doc> = vec![pred_name, this_doc];
                if let SLPropVariant::Init { perm, .. } = variant {
                    args.push(perm.clone());
                }
                args.extend(val_args);
                props.push(naryfn(args));
            }
            TypeT::Refine(ty, p) => {
                self.emit_type_slprop_inner(
                    env,
                    ty,
                    variant,
                    naming,
                    props,
                    this,
                    resolving_struct,
                );
                if let SLPropVariant::Init { .. } = variant {
                    let p = &mut p.clone();
                    self.subst_this_rvalue(env, Rc::make_mut(p), this);
                    props.push(self.emit_rvalue(env, p));
                }
            }
            TypeT::RefineAlways(ty, p) => {
                self.emit_type_slprop_inner(
                    env,
                    ty,
                    variant,
                    naming,
                    props,
                    this,
                    resolving_struct,
                );
                let p = &mut p.clone();
                self.subst_this_rvalue(env, Rc::make_mut(p), this);
                props.push(self.emit_rvalue(env, p));
            }
            TypeT::RefineUninit(ty, p) => {
                self.emit_type_slprop_inner(
                    env,
                    ty,
                    variant,
                    naming,
                    props,
                    this,
                    resolving_struct,
                );
                if let SLPropVariant::Uninit = variant {
                    let p = &mut p.clone();
                    self.subst_this_rvalue(env, Rc::make_mut(p), this);
                    props.push(self.emit_rvalue(env, p));
                }
            }
            TypeT::RefineValue(ty, binding_name, binding_ty, p) => {
                self.emit_type_slprop_inner(
                    env,
                    ty,
                    variant,
                    naming,
                    props,
                    this,
                    resolving_struct,
                );
                if let SLPropVariant::Init { .. } = variant {
                    let binding_type_doc = self.emit_type(env, binding_ty);
                    // RefineValue uses an explicit binding name from the user annotation
                    let raw_name = Doc::text(binding_name.val.to_string());
                    let val_name =
                        self.push_val_binding_explicit(naming, raw_name, binding_type_doc);
                    let _ = val_name; // name is used implicitly in the refinement prop
                    let p = &mut p.clone();
                    self.subst_this_rvalue(env, Rc::make_mut(p), this);
                    let mut env = env.clone();
                    env.push_var_decl(binding_name, binding_ty.clone(), LocalDeclKind::RValue);
                    // Pre-register the binding name in the mangler so it emits without
                    // the "var_" prefix, matching the existential binding name exactly.
                    let name_key = Name::Var(binding_name.val.clone());
                    if !self.nm.map.contains_key(&name_key) {
                        let raw: Rc<str> = Rc::from(&*binding_name.val);
                        self.nm.used.insert(raw.clone());
                        self.nm.map.insert(name_key, raw);
                    }
                    props.push(self.emit_rvalue(&env, p));
                }
            }
            TypeT::Plain(_) => {}
            TypeT::Nullable(inner) => {
                // Collect the inner type's props separately, then wrap the whole
                // conjunction in `unless_null this (…)` so the resource is `emp`
                // when the pointer is null. Val bindings (existentials) are still
                // registered via the shared `naming`.
                let this_doc = self.emit_rvalue(env, this);
                let mut inner_props: Vec<Doc> = vec![];
                self.emit_type_slprop_inner(
                    env,
                    inner,
                    variant,
                    naming,
                    &mut inner_props,
                    this,
                    resolving_struct,
                );
                props.push(annotated(ty, || {
                    naryfn([Doc::text("unless_null"), this_doc, mk_star(inner_props)])
                }));
            }
            TypeT::Error => {}
        }
    }

    /// Collect slprops for a type, register val params, and emit a predicate declaration.
    /// Used by typedef and struct emission for both Init and Uninit variants.
    fn emit_pred_decl(
        &mut self,
        variant: SLPropVariant,
        k: &TypeRefKind,
        base_args: Vec<Doc>,
        emit_slprops: impl Fn(&mut Self, SLPropVariant, &mut ValNaming, &mut Vec<Doc>),
    ) -> Doc {
        let pred_name = match variant {
            SLPropVariant::Init { .. } => self.emit_name(Name::TypeRefPred(k.into())),
            SLPropVariant::Uninit => self.emit_name(Name::TypeRefUninitPred(k.into())),
        };
        let mut args = base_args;
        if let SLPropVariant::Init { .. } = variant {
            args.push(parens(Doc::text("p: perm")));
        }
        let mut bindings = vec![];
        let mut props = vec![];
        let mut naming = ValNaming::Standard {
            quote: false,
            bindings: &mut bindings,
        };
        emit_slprops(self, variant, &mut naming, &mut props);
        drop(naming);
        match variant {
            SLPropVariant::Init { .. } => {
                self.type_val_params.insert(
                    TypeRef::from(k),
                    bindings.iter().map(|b| b.ty.clone()).collect(),
                );
            }
            SLPropVariant::Uninit => {
                self.type_uninit_val_params.insert(
                    TypeRef::from(k),
                    bindings.iter().map(|b| b.ty.clone()).collect(),
                );
            }
        }
        for b in &bindings {
            args.push(parens(
                b.name
                    .clone()
                    .append(":")
                    .append(Doc::line())
                    .append(b.ty.clone()),
            ));
        }
        mk_eager_unfold_slprop(pred_name, &args, mk_star(props))
    }

    fn emit_var(&mut self, v: &Ident) -> Doc {
        annotated(v, || self.emit_name(Name::Var(v.val.clone())))
    }

    fn emit_lvalue(&mut self, env: &Env, v: &Expr) -> Doc {
        match self.emit_expr(env, v) {
            ExprKind::LValue(doc) => doc,
            _ => {
                self.report(format!("cannot produce lvalue for {}", v), &v.loc);
                Doc::text("(admit())")
            }
        }
    }

    fn emit_expr(&mut self, env: &Env, v: &Expr) -> ExprKind {
        match &v.val {
            ExprT::Var(x) => {
                if env.lookup_global_var(x).is_some() {
                    // Global variables need module-qualified names
                    let x2 = annotated(v, || {
                        let mangled = self.nm.mangle(&Name::Var(x.val.clone())).to_string();
                        if let Some(owner_module) = self.fn_module_map.get(&x.val) {
                            if *owner_module == self.current_module {
                                Doc::text(mangled)
                            } else {
                                Doc::text(format!("{}.{}", owner_module, mangled))
                            }
                        } else {
                            Doc::text(mangled)
                        }
                    });
                    ExprKind::RValue(x2)
                } else {
                    let x2 = annotated(v, || self.emit_var(x));
                    if let Some(LocalDecl {
                        kind: LocalDeclKind::RValue,
                        ..
                    }) = env.lookup_var(x)
                    {
                        ExprKind::RValue(x2)
                    } else {
                        ExprKind::LValue(x2)
                    }
                }
            }
            ExprT::Deref(inner) => {
                // *array     → array_read at index 0
                // *arrayptr  → arrayptr_read at index 0
                let inner_kind = env.infer_expr(inner).map(|ty| {
                    if let TypeT::Pointer(_, k) = &env.vtype_whnf(ty).val {
                        Some(k.clone())
                    } else {
                        None
                    }
                });
                let read_fn = match inner_kind {
                    Ok(Some(PointerKind::Array)) => Some("array_read"),
                    Ok(Some(PointerKind::ArrayPtr)) => Some("arrayptr_read"),
                    _ => None,
                };
                if let Some(read_fn) = read_fn {
                    let inner_doc = self.emit_rvalue(env, inner);
                    ExprKind::RValue(annotated(v, || {
                        parens(naryfn([Doc::text(read_fn), inner_doc, Doc::text("0sz")]))
                    }))
                } else {
                    ExprKind::LValue(annotated(v, || self.emit_expr(env, inner).to_rvalue()))
                }
            }
            ExprT::Member(x, a) => match env.infer_expr(x) {
                Ok(ty) => {
                    let ty = env.vtype_whnf(ty);
                    match &ty.val {
                        TypeT::TypeRef(TypeRefKind::Struct(struct_name)) => {
                            let is_inline_array = env
                                .lookup_struct(struct_name)
                                .and_then(|s| s.fields.iter().find(|f| f.val.name().val == a.val))
                                .map(|f| f.val.is_array())
                                .unwrap_or(false);
                            match self.emit_expr(env, x) {
                                ExprKind::ArrayLValue(_) => unreachable!(
                                    "emitting an expression of structure type cannot produce an array"
                                ),
                                ExprKind::LValue(x_doc) => {
                                    if is_inline_array {
                                        // Inline array fields are not stored behind a `ref` —
                                        // the field projection already yields the array handle
                                        // (an rvalue).
                                        ExprKind::ArrayLValue(annotated(v, || {
                                            unaryfn(
                                                self.emit_name(Name::StructFieldProj(
                                                    struct_name.val.clone(),
                                                    a.val.clone(),
                                                )),
                                                x_doc,
                                            )
                                        }))
                                    } else {
                                        ExprKind::LValue(annotated(v, || {
                                            unaryfn(
                                                self.emit_name(Name::StructFieldProj(
                                                    struct_name.val.clone(),
                                                    a.val.clone(),
                                                )),
                                                x_doc,
                                            )
                                        }))
                                    }
                                }
                                ExprKind::RValue(x_doc) => ExprKind::RValue(annotated(v, || {
                                    x_doc.append(Doc::text(".")).append(self.emit_name(
                                        Name::StructDirectFieldName(
                                            struct_name.val.clone(),
                                            a.val.clone(),
                                        ),
                                    ))
                                })),
                            }
                        }
                        TypeT::TypeRef(TypeRefKind::Union(union_name)) => {
                            let is_inline_array = env
                                .lookup_union(union_name)
                                .and_then(|u| u.fields.iter().find(|f| f.val.name().val == a.val))
                                .map(|f| f.val.is_array())
                                .unwrap_or(false);
                            match self.emit_expr(env, x) {
                                ExprKind::ArrayLValue(_) => unreachable!(
                                    "emitting an expression of union type cannot produce an array"
                                ),
                                ExprKind::LValue(x_doc) => {
                                    if is_inline_array {
                                        ExprKind::ArrayLValue(annotated(v, || {
                                            unaryfn(
                                                self.emit_name(Name::UnionFieldProj(
                                                    union_name.val.clone(),
                                                    a.val.clone(),
                                                )),
                                                x_doc,
                                            )
                                        }))
                                    } else {
                                        ExprKind::LValue(unaryfn(
                                            self.emit_name(Name::UnionFieldProj(
                                                union_name.val.clone(),
                                                a.val.clone(),
                                            )),
                                            x_doc,
                                        ))
                                    }
                                }
                                ExprKind::RValue(x_doc) => ExprKind::RValue(annotated(v, || {
                                    parens(
                                        self.emit_name(Name::UnionFieldConstructor(
                                            union_name.val.clone(),
                                            a.val.clone(),
                                        ))
                                        .append("?._0")
                                        .append(Doc::line())
                                        .append(x_doc)
                                        .group(),
                                    )
                                })),
                            }
                        }
                        _ => {
                            self.report(
                                format!("unsupported struct field access on {}", ty),
                                &v.loc,
                            );
                            ExprKind::RValue(annotated(v, || Doc::text("(admit())")))
                        }
                    }
                }
                Err(error) => {
                    self.report(
                        format!("cannot infer type of {}: {}\n{}", x, error, env),
                        &x.loc,
                    );
                    ExprKind::RValue(annotated(v, || Doc::text("(admit())")))
                }
            },
            ExprT::VAttr(VAttr::Length, x) => ExprKind::RValue(annotated(v, || {
                // For FixedArray, emit the statically known length as a plain integer
                let x_ty = env.infer_expr(x).ok().map(|ty| env.vtype_whnf(ty));
                if let Some(ref ty) = x_ty {
                    if let TypeT::FixedArray(_, length) = &ty.val {
                        return Doc::text(format!("{}", length));
                    }
                    // A flexible array member is an inline `array_spec`, so its
                    // length is `array_spec_len` of the stored contents.
                    if matches!(&ty.val, TypeT::FlexArray(_)) {
                        return parens(
                            Doc::text("array_spec_len")
                                .append(Doc::line())
                                .append(self.emit_rvalue(env, x)),
                        );
                    }
                }
                unaryfn(
                    Doc::text("reveal"),
                    unaryfn(Doc::text("length_of"), self.emit_rvalue(env, x)),
                )
            })),
            ExprT::VAttr(VAttr::Active(fld), base) => {
                let base_ty = env.vtype_whnf(env.infer_expr(base).unwrap());
                let TypeT::TypeRef(TypeRefKind::Union(union_name)) = &base_ty.val else {
                    unreachable!()
                };
                let base_doc = self.emit_rvalue(env, base);
                ExprKind::RValue(annotated(v, || {
                    parens(
                        self.emit_name(Name::UnionFieldConstructor(
                            union_name.val.clone(),
                            fld.val.clone(),
                        ))
                        .append("?")
                        .append(Doc::line())
                        .append(base_doc)
                        .group(),
                    )
                }))
            }
            ExprT::Index(arr, idx) => {
                // Check the type of the array expression to decide emission strategy
                let arr_ty = env.infer_expr(arr).ok().map(|ty| env.vtype_whnf(ty));
                let is_fixed_array = arr_ty
                    .as_ref()
                    .is_some_and(|ty| matches!(&ty.val, TypeT::FixedArray(_, _)));
                let is_arrayptr = arr_ty
                    .as_ref()
                    .is_some_and(|ty| matches!(&ty.val, TypeT::Pointer(_, PointerKind::ArrayPtr)));

                // A fixed-array value is a *pure* `array_spec` only when it is an
                // RValue (e.g. a global pure array or a by-value struct field), in
                // which case it must be indexed with `array_spec_idx`. A stack-local
                // array is an LValue holding a runtime `array` handle, so it must be
                // read with `array_read`/`arrayptr_read` like any other live array.
                let arr_kind = self.emit_expr(env, arr);
                let use_spec_idx = is_fixed_array && matches!(arr_kind, ExprKind::RValue(_));
                let arr_doc = match arr_kind {
                    ExprKind::ArrayLValue(arr_doc) => arr_doc,
                    other => other.to_rvalue(),
                };
                let idx_doc = self.emit_rvalue(env, idx);

                if use_spec_idx {
                    // Pure FixedArray value (e.g., global pure array or by-value struct field);
                    // use array_spec_idx for pure indexing
                    ExprKind::RValue(annotated(v, || {
                        parens(naryfn([
                            Doc::text("array_spec_idx"),
                            arr_doc,
                            parens(Doc::text("SizeT.v").append(Doc::line()).append(idx_doc)),
                        ]))
                    }))
                } else {
                    let fn_name = if is_arrayptr {
                        "arrayptr_read"
                    } else {
                        "array_read"
                    };
                    ExprKind::RValue(annotated(v, || {
                        parens(naryfn([Doc::text(fn_name), arr_doc, idx_doc]))
                    }))
                }
            }
            _ => ExprKind::RValue(self.emit_rvalue_inner(env, v)),
        }
    }
} // impl Emitter (group A)

fn binop(a: Doc, op: Doc, b: Doc) -> Doc {
    parens(
        a.append(Doc::line())
            .append(op)
            .group()
            .append(Doc::line())
            .append(b),
    )
}

fn get_int_mod(signed: &bool, width: &u32) -> Option<&'static str> {
    Some(match (signed, width) {
        (false, 8) => "UInt8",
        (false, 16) => "UInt16",
        (false, 32) => "UInt32",
        (false, 64) => "UInt64",

        (true, 8) => "Int8",
        (true, 16) => "Int16",
        (true, 32) => "Int32",
        (true, 64) => "Int64",

        _ => return None,
    })
}

/// Fully-qualified Pulse module providing wrapping (modular) arithmetic for
/// each unsigned width. Referenced fully-qualified because the short module
/// names (`UInt32`, ...) always resolve to `FStar.UIntN`.
fn get_uint_wrap_mod(width: &u32) -> Option<&'static str> {
    Some(match width {
        8 => "Pulse.Lib.C.UInt8",
        16 => "Pulse.Lib.C.UInt16",
        32 => "Pulse.Lib.C.UInt32",
        64 => "Pulse.Lib.C.UInt64",
        _ => return None,
    })
}

/// Fully-qualified bit-field truncation (masking) helper for each unsigned
/// machine width. `mask_uW n v` returns the low `n` bits of `v` as a value
/// provably `< pow2 n` (C unsigned modular truncation on a bit-field write).
fn get_bitfield_mask_fn(machine_width: &u32) -> Option<&'static str> {
    Some(match machine_width {
        8 => "Pulse.Lib.C.BitField.mask_u8",
        16 => "Pulse.Lib.C.BitField.mask_u16",
        32 => "Pulse.Lib.C.BitField.mask_u32",
        64 => "Pulse.Lib.C.BitField.mask_u64",
        _ => return None,
    })
}

fn get_float_mod(width: &u32) -> Option<&'static str> {
    Some(match width {
        32 => "Pulse.Lib.C.float32",
        64 => "Pulse.Lib.C.float64",
        _ => return None,
    })
}

macro_rules! todo_binop {
    () => {
        return None
    };
}

fn emit_unop(env: &Env, op: UnOp, ty: MaybeRc<Type>) -> Option<Doc> {
    Some(match (op, &env.vtype_whnf(ty).val) {
        (UnOp::Not, _) => Doc::text("not"),
        (UnOp::Neg, TypeT::Int { signed, width }) => {
            let modu = get_int_mod(signed, width)?;
            if *signed {
                Doc::text(format!("{}.sub {}.zero", modu, modu))
            } else {
                Doc::text(format!("{}.minus", modu))
            }
        }
        (UnOp::Neg, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("op_Minus"),
        (UnOp::Neg, TypeT::Float { width }) => Doc::text(format!("{}_neg", get_float_mod(width)?)),
        (UnOp::Neg, _) => return None,
        (UnOp::BitNot, TypeT::Int { signed, width }) => {
            Doc::text(format!("{}.lognot", get_int_mod(signed, width)?))
        }
        (UnOp::BitNot, _) => return None,
    })
}

fn emit_binop(env: &Env, op: BinOp, ty: MaybeRc<Type>) -> Option<Doc> {
    Some(match (op, &env.vtype_whnf(ty).val) {
        (BinOp::Eq, TypeT::SLProp | TypeT::Void) => Doc::text("=="),
        (BinOp::Eq, TypeT::Pointer(_, PointerKind::ArrayPtr)) => {
            Doc::text("`Pulse.Lib.C.Array.arrayptr_eq`")
        }
        (BinOp::Eq, TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown)) => {
            Doc::text("`Pulse.Lib.C.Ref.ref_eq`")
        }
        (BinOp::Eq, TypeT::Pointer(_, PointerKind::Core)) => {
            Doc::text("`Pulse.Lib.C.CoreRef.core_ref_eq`")
        }
        (BinOp::Eq, TypeT::Float { width }) => Doc::text(format!("`{}_eq`", get_float_mod(width)?)),
        (
            BinOp::Eq,
            TypeT::SpecInt
            | TypeT::SpecNat
            | TypeT::Bool
            | TypeT::Int { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::Pointer(_, _),
        ) => Doc::text("="),

        (BinOp::LEq, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.lte`", get_int_mod(signed, width)?))
        }
        (BinOp::Lt, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.lt`", get_int_mod(signed, width)?))
        }
        (BinOp::LEq, TypeT::SizeT) => Doc::text("`SizeT.lte`"),
        (BinOp::Lt, TypeT::SizeT) => Doc::text("`SizeT.lt`"),
        (BinOp::LEq, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.lte`"),
        (BinOp::Lt, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.lt`"),
        (BinOp::LEq, TypeT::Float { width }) => {
            Doc::text(format!("`{}_lte`", get_float_mod(width)?))
        }
        (BinOp::Lt, TypeT::Float { width }) => Doc::text(format!("`{}_lt`", get_float_mod(width)?)),
        (BinOp::LEq, TypeT::Pointer(_, PointerKind::ArrayPtr)) => {
            Doc::text("`Pulse.Lib.C.Array.arrayptr_lte`")
        }
        (BinOp::Lt, TypeT::Pointer(_, PointerKind::ArrayPtr)) => {
            Doc::text("`Pulse.Lib.C.Array.arrayptr_lt`")
        }

        (BinOp::LEq, TypeT::Bool) => todo_binop!(),
        (BinOp::Lt, TypeT::Bool) => todo_binop!(),
        (BinOp::LogAnd, TypeT::Bool) => Doc::text("&&"),
        (BinOp::LogOr, TypeT::Bool) => Doc::text("||"),
        (BinOp::Implies, TypeT::Bool) => Doc::text("==>"),
        (BinOp::Div, TypeT::Bool) => todo_binop!(),
        (BinOp::Mod, TypeT::Bool) => todo_binop!(),
        (BinOp::Sub, TypeT::Bool) => todo_binop!(),
        (BinOp::Add, TypeT::Bool) => todo_binop!(),
        (BinOp::Mul, TypeT::Bool) => Doc::text("&&"),

        (BinOp::LogAnd, TypeT::SLProp) => Doc::text("**"),
        (BinOp::LogOr, TypeT::SLProp) => todo_binop!(),
        (BinOp::Implies, TypeT::SLProp) => Doc::text("`Pulse.Lib.Trade.trade`"),

        // Unsigned C arithmetic wraps (modular). Use total wrapping ops with a
        // postcondition that is exact when the result fits and wrapped otherwise.
        // These must precede the generic signed `Int` arms below.
        (
            BinOp::Add,
            TypeT::Int {
                signed: false,
                width,
            },
        ) => Doc::text(format!("`{}.add_wrap`", get_uint_wrap_mod(width)?)),
        (
            BinOp::Sub,
            TypeT::Int {
                signed: false,
                width,
            },
        ) => Doc::text(format!("`{}.sub_wrap`", get_uint_wrap_mod(width)?)),
        (
            BinOp::Mul,
            TypeT::Int {
                signed: false,
                width,
            },
        ) => Doc::text(format!("`{}.mul_wrap`", get_uint_wrap_mod(width)?)),

        (BinOp::Mul, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.mul`", get_int_mod(signed, width)?))
        }
        (BinOp::Mul, TypeT::SizeT) => Doc::text("`SizeT.mul`"),
        (BinOp::Div, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.div`", get_int_mod(signed, width)?))
        }
        (BinOp::Div, TypeT::SizeT) => Doc::text("`SizeT.div`"),
        (BinOp::Mod, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.rem`", get_int_mod(signed, width)?))
        }
        (BinOp::Mod, TypeT::SizeT) => Doc::text("`SizeT.rem`"),
        (BinOp::Add, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.add`", get_int_mod(signed, width)?))
        }
        (BinOp::Add, TypeT::SizeT) => Doc::text("`SizeT.add`"),
        (BinOp::Sub, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.sub`", get_int_mod(signed, width)?))
        }
        (BinOp::Sub, TypeT::SizeT) => Doc::text("`SizeT.sub`"),

        (BinOp::Mul, TypeT::Float { width }) => {
            Doc::text(format!("`{}_mul`", get_float_mod(width)?))
        }
        (BinOp::Div, TypeT::Float { width }) => {
            Doc::text(format!("`{}_div`", get_float_mod(width)?))
        }
        (BinOp::Mod, TypeT::Float { .. }) => todo_binop!(),
        (BinOp::Add, TypeT::Float { width }) => {
            Doc::text(format!("`{}_add`", get_float_mod(width)?))
        }
        (BinOp::Sub, TypeT::Float { width }) => {
            Doc::text(format!("`{}_sub`", get_float_mod(width)?))
        }

        (BinOp::Add, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.add`"),
        (BinOp::Sub, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.sub`"),
        (BinOp::Mul, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.mul`"),
        (BinOp::Div, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.div`"),
        (BinOp::Mod, TypeT::PtrdiffT) => Doc::text("`Pulse.Lib.C.PtrdiffT.rem`"),

        (BinOp::BitAnd, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.logand`", get_int_mod(signed, width)?))
        }
        (BinOp::BitOr, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.logor`", get_int_mod(signed, width)?))
        }
        (BinOp::BitXor, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.logxor`", get_int_mod(signed, width)?))
        }
        (BinOp::Shl, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.shift_left`", get_int_mod(signed, width)?))
        }
        (BinOp::Shr, TypeT::Int { signed, width }) => {
            Doc::text(format!("`{}.shift_right`", get_int_mod(signed, width)?))
        }

        (BinOp::LEq, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("<="),
        (BinOp::Lt, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("<"),
        (BinOp::Mul, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("*"),
        (BinOp::Div, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("/"),
        (BinOp::Mod, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("%"),
        (BinOp::Add, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("+"),
        (BinOp::Sub, TypeT::SpecInt | TypeT::SpecNat) => Doc::text("-"),
        (BinOp::LogAnd, TypeT::SpecInt | TypeT::SpecNat) => todo_binop!(),
        (BinOp::LogOr, TypeT::SpecInt | TypeT::SpecNat) => todo_binop!(),
        (BinOp::Implies, TypeT::SpecInt | TypeT::SpecNat) => todo_binop!(),
        (
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr,
            TypeT::SpecInt | TypeT::SpecNat,
        ) => {
            todo_binop!()
        }

        (
            op,
            TypeT::Refine(ty, _)
            | TypeT::RefineAlways(ty, _)
            | TypeT::RefineUninit(ty, _)
            | TypeT::RefineValue(ty, ..)
            | TypeT::Plain(ty)
            | TypeT::Nullable(ty),
        ) => emit_binop(env, op, ty.clone().into())?,

        (_, TypeT::TypeRef(_)) => return None,
        (
            BinOp::LEq
            | BinOp::Lt
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::Add
            | BinOp::Sub
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Shl
            | BinOp::Shr,
            TypeT::Pointer(..),
        )
        | (_, TypeT::Void)
        | (
            BinOp::LogAnd | BinOp::LogOr | BinOp::Implies,
            TypeT::Int { .. }
            | TypeT::Float { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::Pointer(..),
        )
        | (
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr,
            TypeT::Bool | TypeT::Float { .. } | TypeT::SizeT | TypeT::PtrdiffT,
        )
        | (_, TypeT::SLProp)
        | (_, TypeT::Error)
        | (_, TypeT::Unknown)
        | (_, TypeT::FnPtr { .. })
        | (_, TypeT::FixedArray(_, _))
        | (_, TypeT::FlexArray(_)) => return None,
    })
}

impl<'a> Emitter<'a> {
    fn emit_rvalue(&mut self, env: &Env, v: &Expr) -> Doc {
        self.emit_expr(env, v).to_rvalue_decayed()
    }

    fn emit_pattern(&mut self, env: &Env, pattern: &Expr) -> Doc {
        if let ExprT::IntLit(val, ty) = &pattern.val {
            let resolved = env.vtype_whnf(ty.clone().into());
            let literal = match resolved.val {
                TypeT::Int {
                    signed: true,
                    width: 8,
                } => Some(format!("{}y", val)),
                TypeT::Int {
                    signed: false,
                    width: 8,
                } => Some(format!("{}uy", normalize_unsigned(val, 8))),
                TypeT::Int {
                    signed: true,
                    width: 16,
                } => Some(format!("{}s", val)),
                TypeT::Int {
                    signed: false,
                    width: 16,
                } => Some(format!("{}us", normalize_unsigned(val, 16))),
                TypeT::Int {
                    signed: true,
                    width: 32,
                } => Some(format!("{}l", val)),
                TypeT::Int {
                    signed: false,
                    width: 32,
                } => Some(format!("{}ul", normalize_unsigned(val, 32))),
                TypeT::Int {
                    signed: true,
                    width: 64,
                } => Some(format!("{}L", val)),
                TypeT::Int {
                    signed: false,
                    width: 64,
                } => Some(format!("{}uL", normalize_unsigned(val, 64))),
                TypeT::SizeT => Some(format!("{}sz", val)),
                _ => None,
            };
            if let Some(literal) = literal {
                return Doc::text(literal);
            }
        }
        self.emit_rvalue(env, pattern)
    }

    fn emit_rvalue_inner(&mut self, env: &Env, v: &Expr) -> Doc {
        annotated(v, || {
            match &v.val {
                ExprT::BoolLit(v) => Doc::text(if *v { "true" } else { "false" }),
                ExprT::IntLit(val, ty) => {
                    let resolved = env.vtype_whnf(ty.clone().into());
                    match resolved.val {
                        TypeT::Int {
                            signed: true,
                            width: 32,
                        } => Doc::text(format!("{}l", val)),
                        TypeT::Int {
                            signed: false,
                            width: 32,
                        } => {
                            // clang hands us the signed interpretation of the
                            // bit pattern (see toBigInt in cpp/impl.cpp), so a
                            // u32 literal with the high bit set arrives as a
                            // negative BigInt (e.g. 0xFFFFFFFF as -1). F*'s `ul`
                            // literals must lie in [0, 2^32), so normalize first.
                            Doc::text(format!("{}ul", normalize_unsigned(val, 32)))
                        }
                        TypeT::Int {
                            signed: true,
                            width,
                        } => Doc::text(format!("(Int{}.int_to_t {})", width, val)),
                        TypeT::Int {
                            signed: false,
                            width,
                        } => Doc::text(format!(
                            "(UInt{}.uint_to_t {})",
                            width,
                            normalize_unsigned(val, width)
                        )),
                        TypeT::SizeT => Doc::text(format!("{}sz", val)),
                        TypeT::SpecInt | TypeT::SpecNat => Doc::text(format!("{}", val)),
                        TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown)
                            if **val == BigInt::ZERO =>
                        {
                            Doc::text("null")
                        }
                        TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                            if **val == BigInt::ZERO =>
                        {
                            Doc::text("array_null")
                        }
                        TypeT::Pointer(_, PointerKind::Core) if **val == BigInt::ZERO => {
                            Doc::text("core_null")
                        }
                        TypeT::FnPtr { .. } if **val == BigInt::ZERO => {
                            Doc::text("Pulse.Lib.C.FuncPtr.null _ _")
                        }
                        _ => {
                            self.report(
                                format!("unsupported integer literal type for {}", val),
                                &v.loc,
                            );
                            Doc::text(format!("(admit()) (* {} *)", val))
                        }
                    }
                }
                ExprT::FloatLit(val, ty) => {
                    let resolved = env.vtype_whnf(ty.clone().into());
                    match resolved.val {
                        TypeT::Float { width: 32 } => unaryfn(
                            Doc::text("Pulse.Lib.C.float32_of_string"),
                            Doc::text(format!("{:?}", val.to_string())),
                        ),
                        TypeT::Float { width: 64 } => unaryfn(
                            Doc::text("Pulse.Lib.C.float64_of_string"),
                            Doc::text(format!("{:?}", val.to_string())),
                        ),
                        _ => {
                            self.report(
                                format!("unsupported floating literal type for {}", val),
                                &v.loc,
                            );
                            Doc::text("(admit())")
                        }
                    }
                }
                ExprT::Var(_)
                | ExprT::Deref(_)
                | ExprT::Member(_, _)
                | ExprT::VAttr(_, _)
                | ExprT::Index(_, _) => {
                    // These are lvalue/vattr variants; handled by emit_expr
                    unreachable!("lvalue/vattr variants should be handled by emit_expr")
                }
                ExprT::Ref(v) => {
                    // `&g` for a `_pure` global: the global is a plain F* value
                    // with no lvalue, so use its assumed address. Ownership is
                    // acquired by the caller with `acquire_var_g` and released
                    // with `drop_`.
                    if let ExprT::Var(x) = &v.val
                        && env.addressable_global(x).is_some()
                    {
                        return self.emit_name(Name::GlobalAddr(x.val.clone()));
                    }
                    self.emit_lvalue(env, v)
                }
                ExprT::Cast(val, to_ty) => {
                    let val_doc = self.emit_rvalue(env, val);
                    let Ok(from_ty) = env.infer_expr(val).map(|t| env.vtype_whnf(t)) else {
                        // If we can't infer the type, we should have logged an error somewhere else.
                        return val_doc;
                    };
                    let to_ty = env.vtype_whnf(to_ty.clone().into());
                    // Special case: integer literal cast to SizeT → emit Nsz
                    if matches!(&to_ty.val, TypeT::SizeT) {
                        if let ExprT::IntLit(n, _) = &val.val {
                            return Doc::text(format!("{}sz", n));
                        }
                    }
                    if env.vtype_eq(from_ty.clone(), to_ty.clone()) {
                        // Same underlying type, no cast necessary.
                        return val_doc;
                    }
                    let default_msg = format!("unsupported cast from {} to {}", from_ty, to_ty);
                    match (&from_ty.val, &to_ty.val) {
                        (TypeT::Bool, TypeT::Int { signed, width }) => {
                            fn abbrev(s: &bool, w: &u32) -> String {
                                format!("{}int{}", if *s { "" } else { "u" }, w)
                            }
                            unaryfn(
                                Doc::text(format!("bool_to_{}", abbrev(signed, width))),
                                val_doc,
                            )
                        }
                        (TypeT::Bool, TypeT::SpecInt | TypeT::SpecNat) => {
                            unaryfn(Doc::text("bool_to_int"), val_doc)
                        }
                        (TypeT::SpecInt | TypeT::SpecNat, TypeT::Bool) => parens(
                            val_doc
                                .append(Doc::line())
                                .append("<>")
                                .append(Doc::line())
                                .append("0"),
                        ),
                        (TypeT::SpecNat, TypeT::SpecInt) => with_type(val_doc, Doc::text("int")),
                        (TypeT::SpecInt, TypeT::SpecNat) => with_type(val_doc, Doc::text("nat")),
                        (TypeT::Bool, TypeT::SizeT) => parens(
                            Doc::text("if")
                                .append(Doc::line())
                                .append(val_doc)
                                .group()
                                .append(Doc::line())
                                .append("then")
                                .append(Doc::line().append("1sz").nest(2))
                                .append(Doc::line())
                                .append("else")
                                .append(Doc::line().append("0sz").nest(2)),
                        ),
                        (TypeT::Bool, TypeT::SLProp) => unaryfn(Doc::text("with_pure"), val_doc),
                        (TypeT::Bool, TypeT::Float { width }) => {
                            if let Some(m) = get_float_mod(width) {
                                unaryfn(Doc::text(format!("{}_of_bool", m)), val_doc)
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Int { signed, width }, TypeT::Bool) => {
                            fn abbrev(s: &bool, w: &u32) -> String {
                                format!("{}int{}", if *s { "" } else { "u" }, w)
                            }
                            unaryfn(
                                Doc::text(format!("{}_to_bool", abbrev(signed, width))),
                                val_doc,
                            )
                        }
                        (
                            TypeT::Int {
                                signed: s1,
                                width: w1,
                            },
                            TypeT::Int {
                                signed: s2,
                                width: w2,
                            },
                        ) if s1 == s2 && w1 == w2 => val_doc,
                        (TypeT::Int { signed, width }, TypeT::SpecInt | TypeT::SpecNat) => {
                            if let Some(m) = get_int_mod(signed, width) {
                                unaryfn_with_type(
                                    Doc::text(format!("{}.v", m)),
                                    val_doc,
                                    Doc::text("int"),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Float { width }, TypeT::Bool) => {
                            if let Some(m) = get_float_mod(width) {
                                unaryfn(Doc::text(format!("{}_to_bool", m)), val_doc)
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Float { width: 32 }, TypeT::Float { width: 64 }) => unaryfn(
                            Doc::text("Pulse.Lib.C.float64_of_int (Pulse.Lib.C.float32_to_int"),
                            val_doc.append(Doc::text(")")),
                        ),
                        (TypeT::Float { width: 64 }, TypeT::Float { width: 32 }) => unaryfn(
                            Doc::text("Pulse.Lib.C.float32_of_int (Pulse.Lib.C.float64_to_int"),
                            val_doc.append(Doc::text(")")),
                        ),
                        (TypeT::Float { width: w1 }, TypeT::Float { width: w2 }) if w1 == w2 => {
                            val_doc
                        }
                        (TypeT::Int { signed, width }, TypeT::Float { width: fw }) => {
                            if let (Some(int_mod), Some(float_mod)) =
                                (get_int_mod(signed, width), get_float_mod(fw))
                            {
                                unaryfn(
                                    Doc::text(format!("{}_of_int ({}.v", float_mod, int_mod)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Float { width: fw }, TypeT::Int { signed, width }) => {
                            if let (Some(float_mod), Some(int_mod)) =
                                (get_float_mod(fw), get_int_mod(signed, width))
                            {
                                unaryfn(
                                    Doc::text(format!(
                                        "{}.{} ({}_to_int",
                                        int_mod,
                                        if *signed { "int_to_t" } else { "uint_to_t" },
                                        float_mod
                                    )),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
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
                            fn abbrev(s: bool, w: u32) -> String {
                                format!("{}int{}", if s { "" } else { "u" }, w)
                            }
                            unaryfn_with_type(
                                Doc::text(format!(
                                    "Int.Cast.{}_to_{}",
                                    abbrev(*s1, *w1),
                                    abbrev(*s2, *w2)
                                )),
                                val_doc,
                                self.emit_type(env, &*to_ty),
                            )
                        }
                        (TypeT::SizeT, TypeT::SpecInt | TypeT::SpecNat) => {
                            unaryfn(Doc::text("SizeT.v"), val_doc)
                        }
                        (TypeT::SizeT, TypeT::Int { signed, width }) => {
                            if let Some(m) = get_int_mod(signed, width) {
                                unaryfn(
                                    Doc::text(format!(
                                        "{}.{} (SizeT.v",
                                        m,
                                        if *signed { "int_to_t" } else { "uint_to_t" }
                                    )),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Int { signed, width }, TypeT::SizeT) => {
                            if let Some(m) = get_int_mod(signed, width) {
                                unaryfn(
                                    Doc::text(format!("SizeT.uint_to_t ({}.v", m)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::SpecInt | TypeT::SpecNat, TypeT::SizeT) => {
                            unaryfn(Doc::text("SizeT.uint_to_t"), val_doc)
                        }
                        (TypeT::SpecInt | TypeT::SpecNat, TypeT::Int { signed, width }) => {
                            if let Some(m) = get_int_mod(signed, width) {
                                unaryfn(
                                    Doc::text(format!(
                                        "{}.{}",
                                        m,
                                        if *signed { "int_to_t" } else { "uint_to_t" }
                                    )),
                                    val_doc,
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        // (TypeT::Int { signed:s1, width:w1 }, TypeT::Int { signed:s2, width:w2 }) => todo!(),
                        // (TypeT::Int { signed, width }, TypeT::SizeT) => todo!(),
                        // (TypeT::Int { signed, width }, TypeT::SLProp) => todo!(),
                        (TypeT::SizeT, TypeT::Bool) => binop(
                            unaryfn(Doc::text("SizeT.v"), val_doc),
                            Doc::text("<>"),
                            Doc::text("0"),
                        ),
                        // (TypeT::SizeT, TypeT::SLProp) => todo!(),
                        // (TypeT::Pointer { to, kind }, TypeT::Bool) => todo!(),
                        (TypeT::Pointer(_, kind), TypeT::Bool) => {
                            let is_null_fn = match kind {
                                PointerKind::Array | PointerKind::ArrayPtr => "array_is_null",
                                PointerKind::Core => "Pulse.Lib.C.CoreRef.core_is_null",
                                _ => "Pulse.Lib.Reference.is_null",
                            };
                            unaryfn(Doc::text("not"), unaryfn(Doc::text(is_null_fn), val_doc))
                        }
                        (TypeT::FnPtr { .. }, TypeT::Bool) => {
                            // `if (fp)` truthiness: read the pointer value and
                            // test it against null. The ref keeps ordinary
                            // `pts_to`, so the raw `is_null (!r)` deref frames
                            // directly — no `valid_ptr`-aware variant needed.
                            // (A `_nullable` guard that must *refine* validity in
                            // the taken branch is future work.)
                            unaryfn(
                                Doc::text("not"),
                                unaryfn(Doc::text("Pulse.Lib.C.FuncPtr.is_null"), val_doc),
                            )
                        }
                        // (TypeT::Pointer { to, kind }, TypeT::SizeT) => todo!(),
                        (_, TypeT::Pointer(_, to_kind)) if matches!(&val.val, ExprT::IntLit(n, _) if **n == BigInt::ZERO) => {
                            match to_kind {
                                PointerKind::Ref | PointerKind::Unknown => Doc::text("null"),
                                PointerKind::Array | PointerKind::ArrayPtr => {
                                    Doc::text("array_null")
                                }
                                PointerKind::Core => Doc::text("core_null"),
                            }
                        }
                        (_, TypeT::FnPtr { .. }) if matches!(&val.val, ExprT::IntLit(n, _) if **n == BigInt::ZERO) => {
                            Doc::text("Pulse.Lib.C.FuncPtr.null _ _")
                        }
                        // (TypeT::Pointer { to:t1, kind:k1 }, TypeT::Pointer { to:t2, kind:k2 }) if t1 == t2 => todo!(),
                        // (TypeT::Pointer { to, kind }, TypeT::SLProp) => todo!(),
                        (TypeT::PtrdiffT, TypeT::SizeT) => unaryfn(
                            Doc::text("SizeT.uint_to_t (Pulse.Lib.C.PtrdiffT.v"),
                            val_doc.append(Doc::text(")")),
                        ),
                        (TypeT::SizeT, TypeT::PtrdiffT) => unaryfn(
                            Doc::text("Pulse.Lib.C.PtrdiffT.of_int (SizeT.v"),
                            val_doc.append(Doc::text(")")),
                        ),
                        (TypeT::SizeT, TypeT::Float { width }) => {
                            if let Some(m) = get_float_mod(width) {
                                unaryfn(
                                    Doc::text(format!("{}_of_int (SizeT.v", m)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Float { width }, TypeT::SizeT) => {
                            if let Some(m) = get_float_mod(width) {
                                unaryfn(
                                    Doc::text(format!("SizeT.uint_to_t ({}_to_int", m)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Int { signed, width }, TypeT::PtrdiffT) => {
                            if let Some(m) = get_int_mod(signed, width) {
                                unaryfn(
                                    Doc::text(format!("Pulse.Lib.C.PtrdiffT.of_int ({}.v", m)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::PtrdiffT, TypeT::Int { signed, width }) => {
                            if let Some(m) = get_int_mod(signed, width) {
                                unaryfn(
                                    Doc::text(format!(
                                        "{}.{} (Pulse.Lib.C.PtrdiffT.v",
                                        m,
                                        if *signed { "int_to_t" } else { "uint_to_t" }
                                    )),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::PtrdiffT, TypeT::PtrdiffT) => val_doc,
                        (TypeT::PtrdiffT, TypeT::Float { width }) => {
                            if let Some(m) = get_float_mod(width) {
                                unaryfn(
                                    Doc::text(format!("{}_of_int (Pulse.Lib.C.PtrdiffT.v", m)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        (TypeT::Float { width }, TypeT::PtrdiffT) => {
                            if let Some(m) = get_float_mod(width) {
                                unaryfn(
                                    Doc::text(format!("Pulse.Lib.C.PtrdiffT.of_int ({}_to_int", m)),
                                    val_doc.append(Doc::text(")")),
                                )
                            } else {
                                self.report(default_msg.clone(), &v.loc);
                                Doc::text("(admit())")
                            }
                        }
                        // FixedArray → Pointer(Array): array-to-pointer decay (identity in Pulse)
                        (
                            TypeT::FixedArray(_, _),
                            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr),
                        ) => val_doc,
                        // A fixed array can decay to an ordinary C pointer.
                        (
                            TypeT::FixedArray(_, _),
                            TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown),
                        ) => {
                            let fn_name = if matches!(
                                &val.val,
                                ExprT::ArrayInit {
                                    is_static: true,
                                    ..
                                }
                            ) {
                                // String literals have static storage duration,
                                // unlike local fixed-size arrays.
                                "Pulse.Lib.C.Array.array_literal_to_ref"
                            } else {
                                "Pulse.Lib.C.Array.array_to_ref"
                            };
                            unaryfn(Doc::text(fn_name), val_doc)
                        }
                        // `core_ref` (raw `_core_ref` back-pointer) → typed `ref T`:
                        // recover the typed reference. The pointee type is known
                        // from the cast target. Mirrors array_to_arrayptr below.
                        (
                            TypeT::Pointer(_, PointerKind::Core),
                            TypeT::Pointer(to_pointee, PointerKind::Ref | PointerKind::Unknown),
                        ) => parens(naryfn([
                            Doc::text("Pulse.Lib.C.CoreRef.core_to_ref"),
                            self.emit_type(env, to_pointee),
                            val_doc,
                        ])),
                        // typed `ref T` → `core_ref`: erase the pointee type.
                        (
                            TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown),
                            TypeT::Pointer(_, PointerKind::Core),
                        ) => unaryfn(Doc::text("Pulse.Lib.C.CoreRef.ref_to_core"), val_doc),
                        // array/arrayptr → `core_ref`: convert the arrayptr to a
                        // `ref` of the same handle (`array_to_ref`, the identity
                        // coercion) and erase it to the raw base+offset address
                        // with the single `ref_to_core` primitive. Emitted for a
                        // mixed arrayptr/ref `==`, so the two pointer kinds
                        // compare via `core_ref_eq`.
                        (
                            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr),
                            TypeT::Pointer(_, PointerKind::Core),
                        ) => unaryfn(
                            Doc::text("Pulse.Lib.C.CoreRef.ref_to_core"),
                            unaryfn(Doc::text("Pulse.Lib.C.Array.array_to_ref"), val_doc),
                        ),
                        (TypeT::Pointer(_, _), TypeT::Pointer(_, to_kind)) => {
                            // Pointer kind change (e.g., Ref→ArrayPtr for null)
                            if matches!(&val.val, ExprT::IntLit(n, _) if **n == BigInt::ZERO) {
                                match to_kind {
                                    PointerKind::Ref | PointerKind::Unknown => Doc::text("null"),
                                    PointerKind::Array | PointerKind::ArrayPtr => {
                                        Doc::text("array_null")
                                    }
                                    PointerKind::Core => Doc::text("core_null"),
                                }
                            } else if matches!(to_kind, PointerKind::ArrayPtr) {
                                // Array→ArrayPtr: obtain arrayptr_pts_to resource
                                parens(naryfn([
                                    Doc::text("array_to_arrayptr"),
                                    val_doc,
                                    Doc::text("0sz"),
                                ]))
                            } else {
                                val_doc
                            }
                        }
                        (TypeT::Error | TypeT::Unknown, _) | (_, TypeT::Error | TypeT::Unknown) => {
                            val_doc
                        }
                        _ => {
                            self.report(default_msg.clone(), &v.loc);
                            Doc::text("(admit())")
                        }
                    }
                }
                ExprT::Error(_ty) => Doc::text("(admit())"),
                ExprT::InlinePulse(val, _) => {
                    let env = &mut env.clone();
                    parens(self.emit_inline_pulse_tokens(env, val))
                }
                ExprT::BinOp(BinOp::LogAnd, lhs, rhs) => {
                    if let Ok(ty) = env.infer_expr(lhs) {
                        if ty.val == TypeT::SLProp {
                            return binop(
                                self.emit_rvalue(env, lhs),
                                Doc::text("**"),
                                self.emit_rvalue(env, rhs),
                            );
                        }
                    }
                    binop(
                        self.emit_rvalue(env, lhs),
                        Doc::text("&&"),
                        self.emit_rvalue(env, rhs),
                    )
                }
                ExprT::BinOp(BinOp::LogOr, lhs, rhs) => binop(
                    self.emit_rvalue(env, lhs),
                    Doc::text("||"),
                    self.emit_rvalue(env, rhs),
                ),
                ExprT::BinOp(BinOp::Eq, lhs, rhs) => {
                    if let Ok(ty) = env.infer_expr(lhs) {
                        let ty = env.vtype_whnf(ty);
                        match (&ty.val, &rhs.val) {
                            (
                                TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown),
                                ExprT::IntLit(n, _),
                            ) => {
                                if **n == BigInt::ZERO {
                                    return unaryfn(
                                        Doc::text("Pulse.Lib.Reference.is_null"),
                                        self.emit_rvalue(env, lhs),
                                    );
                                }
                            }
                            (
                                TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr),
                                ExprT::IntLit(n, _),
                            ) => {
                                if **n == BigInt::ZERO {
                                    return unaryfn(
                                        Doc::text("array_is_null"),
                                        self.emit_rvalue(env, lhs),
                                    );
                                }
                            }
                            (TypeT::Pointer(_, PointerKind::Core), ExprT::IntLit(n, _)) => {
                                if **n == BigInt::ZERO {
                                    return unaryfn(
                                        Doc::text("Pulse.Lib.C.CoreRef.core_is_null"),
                                        self.emit_rvalue(env, lhs),
                                    );
                                }
                            }
                            (TypeT::FnPtr { .. }, ExprT::IntLit(n, _)) => {
                                if **n == BigInt::ZERO {
                                    // `fp == 0`: read the pointer value and test
                                    // it against null. The ref keeps ordinary
                                    // `pts_to`, so the raw `is_null (!r)` frames.
                                    return unaryfn(
                                        Doc::text("Pulse.Lib.C.FuncPtr.is_null"),
                                        self.emit_rvalue(env, lhs),
                                    );
                                }
                            }
                            _ => {}
                        }
                    }
                    // For non-null pointer equality, use the emit_binop path
                    // which dispatches to ref_eq / arrayptr_eq as appropriate.
                    if let Ok(ty) = env.infer_expr(lhs) {
                        if let Some(op_doc) = emit_binop(env, BinOp::Eq, ty) {
                            return binop(
                                self.emit_rvalue(env, lhs),
                                op_doc,
                                self.emit_rvalue(env, rhs),
                            );
                        }
                    }
                    // TODO: this should be == in ghost contexts
                    binop(
                        self.emit_rvalue(env, lhs),
                        Doc::text("="),
                        self.emit_rvalue(env, rhs),
                    )
                }
                ExprT::UnOp(op, arg) => {
                    if let Ok(ty) = env.infer_expr(&arg)
                        && let Some(op) = emit_unop(env, *op, ty)
                    {
                        unaryfn(op, self.emit_rvalue(env, arg))
                    } else {
                        self.report(format!("unsupported unary operator on {}", arg), &v.loc);
                        Doc::text("(admit())")
                    }
                }
                ExprT::BinOp(op, lhs, rhs) => {
                    // Pointer arithmetic: ptr + int → arrayptr_shift / array_to_arrayptr
                    if *op == BinOp::Add {
                        let lhs_ty = env.infer_expr(lhs).ok().map(|t| env.vtype_whnf(t));
                        let rhs_ty = env.infer_expr(rhs).ok().map(|t| env.vtype_whnf(t));
                        let lhs_is_ptr = lhs_ty.as_ref().is_some_and(|t| {
                            matches!(
                                t.val,
                                TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                            )
                        });
                        let rhs_is_ptr = rhs_ty.as_ref().is_some_and(|t| {
                            matches!(
                                t.val,
                                TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                            )
                        });
                        if lhs_is_ptr {
                            let is_array = lhs_ty.as_ref().is_some_and(|t| {
                                matches!(t.val, TypeT::Pointer(_, PointerKind::Array))
                            });
                            let fn_name = if is_array {
                                "array_to_arrayptr"
                            } else {
                                "arrayptr_shift"
                            };
                            return parens(naryfn([
                                Doc::text(fn_name),
                                self.emit_rvalue(env, lhs),
                                self.emit_rvalue(env, rhs),
                            ]));
                        } else if rhs_is_ptr {
                            let is_array = rhs_ty.as_ref().is_some_and(|t| {
                                matches!(t.val, TypeT::Pointer(_, PointerKind::Array))
                            });
                            let fn_name = if is_array {
                                "array_to_arrayptr"
                            } else {
                                "arrayptr_shift"
                            };
                            return parens(naryfn([
                                Doc::text(fn_name),
                                self.emit_rvalue(env, rhs),
                                self.emit_rvalue(env, lhs),
                            ]));
                        }
                    }
                    // Pointer subtraction: ptr - ptr → arrayptr_diff
                    if *op == BinOp::Sub {
                        let lhs_ty = env.infer_expr(lhs).ok().map(|t| env.vtype_whnf(t));
                        let rhs_ty = env.infer_expr(rhs).ok().map(|t| env.vtype_whnf(t));
                        let lhs_is_ptr = lhs_ty.as_ref().is_some_and(|t| {
                            matches!(
                                t.val,
                                TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                            )
                        });
                        let rhs_is_ptr = rhs_ty.as_ref().is_some_and(|t| {
                            matches!(
                                t.val,
                                TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                            )
                        });
                        if lhs_is_ptr && rhs_is_ptr {
                            return parens(naryfn([
                                Doc::text("arrayptr_diff"),
                                self.emit_rvalue(env, lhs),
                                self.emit_rvalue(env, rhs),
                            ]));
                        }
                    }
                    if let Ok(ty) = env.infer_expr(&lhs)
                        && let Some(op) = emit_binop(env, *op, ty)
                    {
                        binop(self.emit_rvalue(env, lhs), op, self.emit_rvalue(env, rhs))
                    } else {
                        self.report(format!("unsupported binary operator on {}", lhs), &v.loc);
                        Doc::text("(admit())")
                    }
                }
                ExprT::FnCall(f, args) => {
                    let args = if args.is_empty() {
                        Doc::text("()")
                    } else {
                        Doc::intersperse(
                            args.iter().map(|arg| self.emit_rvalue(env, arg)),
                            Doc::line(),
                        )
                    };
                    parens(
                        self.emit_name(Name::Fn(f.val.clone()))
                            .append(Doc::line())
                            .append(args),
                    )
                }
                ExprT::FnRef(g) => {
                    // A function-to-pointer decay (`add` / `&add`): the concrete
                    // function-pointer value `of_fn (pre_of func_<g>__fp)
                    // (post_of func_<g>__fp) func_<g>__fp` (see `emit_of_fn`).
                    // Emitting the resolved `of_fn` term (rather than an abstract
                    // handle) is what lets `of_fn_valid`'s SMTPat discharge
                    // validity at the call site.
                    self.emit_of_fn(env, g)
                }
                ExprT::FnPtrCall(f, args) => {
                    // Indirect call `fp(args)`. We evaluate the callee to a
                    // `func_ptr` *value* (an `!r` read for a mutable local, or the
                    // bare value for a parameter/temporary) and hand it to the
                    // value-form primitive `call` (total body) or `call_div`
                    // (divergent body). The primitive takes the validity spec
                    // `pre`/`post` explicitly (SMT cannot solve for the
                    // higher-order predicate). With no annotation to supply them,
                    // we emit inference holes `_ _`: the call type-checks
                    // structurally and, when an `is_valid <value> <div> ..` fact is
                    // in scope (seeded by `of_fn_valid`/`of_fn_div_valid`, or
                    // carried in a callback parameter's precondition), the holes
                    // unify against it.
                    let arg_tuple = self.emit_fnptr_arg_tuple(env, args);
                    let callee_val = self.emit_rvalue(env, f);
                    let call_prim = if self.current_fn_total {
                        "Pulse.Lib.C.FuncPtr.call"
                    } else {
                        "Pulse.Lib.C.FuncPtr.call_div"
                    };
                    parens(naryfn([
                        Doc::text(call_prim),
                        Doc::text("_"),
                        Doc::text("_"),
                        callee_val,
                        arg_tuple,
                    ]))
                }
                ExprT::Live(v) => {
                    // Check if the dereferenced expression is an array type
                    let is_array = if let ExprT::Deref(inner) = &v.val {
                        env.infer_expr(inner)
                            .map(|ty| {
                                matches!(
                                    env.vtype_whnf(ty).val,
                                    TypeT::Pointer(_, PointerKind::Array)
                                )
                            })
                            .unwrap_or(false)
                    } else {
                        false
                    };
                    let is_arrayptr = if let ExprT::Deref(inner) = &v.val {
                        env.infer_expr(inner)
                            .map(|ty| {
                                matches!(
                                    env.vtype_whnf(ty).val,
                                    TypeT::Pointer(_, PointerKind::ArrayPtr)
                                )
                            })
                            .unwrap_or(false)
                    } else {
                        false
                    };
                    if is_arrayptr {
                        // arrayptrs carry no permissions; _live is emp
                        Doc::text("emp")
                    } else if is_array {
                        // Extract the inner expression from `*arr` and pass its
                        // rvalue (the array handle itself) to live_array.
                        // `ExprT::Deref` for Array now returns an RValue
                        // (array_read ... 0sz), so emit_lvalue would fail.
                        let ExprT::Deref(inner) = &v.val else {
                            unreachable!("is_array implies v is a Deref")
                        };
                        unaryfn(
                            Doc::text("Pulse.Lib.C.Array.live_array"),
                            self.emit_rvalue(env, inner),
                        )
                    } else {
                        unaryfn(Doc::text("live"), self.emit_lvalue(env, v))
                    }
                }
                ExprT::Old(v) => unaryfn(Doc::text("old"), self.emit_rvalue(env, v)),
                ExprT::Forall(var, ty, body) | ExprT::Exists(var, ty, body) => {
                    let mut env = env.clone();
                    env.push_var_decl(var, ty.clone(), LocalDeclKind::RValue);
                    let is_slprop = if let Ok(body_ty) = env.infer_expr(body) {
                        env.is_slprop(body_ty)
                    } else {
                        false
                    };
                    let keyword = match &v.val {
                        ExprT::Forall(..) => {
                            if is_slprop {
                                "forall*"
                            } else {
                                "forall"
                            }
                        }
                        _ => {
                            if is_slprop {
                                "exists*"
                            } else {
                                "exists"
                            }
                        }
                    };
                    parens(
                        Doc::text(keyword)
                            .append(Doc::line())
                            .append(parens(
                                self.emit_name(Name::Var(var.val.clone()))
                                    .append(":")
                                    .append(Doc::space())
                                    .append(self.emit_type(&env, ty)),
                            ))
                            .append(".")
                            .append(Doc::line())
                            .append(self.emit_rvalue(&env, body)),
                    )
                }
                ExprT::StructInit(name, fields) => {
                    // Emit every field of the struct in declaration order: use
                    // the provided initializer if present, otherwise the field's
                    // zero default. This handles fields omitted from a C
                    // compound literal — notably a flexible array member, which
                    // cannot be initialized in C and defaults to a length-0
                    // array (`array_spec_zeroed elem 0 ..`).
                    let sdef = env.lookup_struct(name).cloned();
                    let entries: Vec<Doc> = if let Some(sdef) = sdef {
                        sdef.fields
                            .iter()
                            .map(|f| {
                                let fname = f.val.name().val.clone();
                                let val_doc = if let Some((_, val)) =
                                    fields.iter().find(|(fld, _)| fld.val == fname)
                                {
                                    self.emit_rvalue(env, val)
                                } else {
                                    self.emit_field_default(env, f)
                                };
                                Doc::line()
                                    .append(self.emit_name(Name::StructDirectFieldName(
                                        name.val.clone(),
                                        fname,
                                    )))
                                    .append("=")
                                    .append(val_doc)
                                    .append(";")
                            })
                            .collect()
                    } else {
                        fields
                            .iter()
                            .map(|(fld, val)| {
                                Doc::line()
                                    .append(self.emit_name(Name::StructDirectFieldName(
                                        name.val.clone(),
                                        fld.val.clone(),
                                    )))
                                    .append("=")
                                    .append(self.emit_rvalue(env, val))
                                    .append(";")
                            })
                            .collect()
                    };
                    Doc::text("{")
                        .append(Doc::concat(entries))
                        .nest(2)
                        .append(Doc::line())
                        .append("}")
                        .group()
                }
                ExprT::UnionInit(name, fld, val) => unaryfn(
                    self.emit_name(Name::UnionFieldConstructor(
                        name.val.clone(),
                        fld.val.clone(),
                    )),
                    self.emit_rvalue(env, val),
                ),
                ExprT::ArrayInit { elem_ty, elems, .. } => {
                    let elem_ty_doc = self.emit_type(env, elem_ty);
                    let elem_ty_arg = Doc::text("#").append(elem_ty_doc);
                    naryfn([
                        Doc::text("array_spec_of_list_with_len"),
                        elem_ty_arg.clone(),
                        // Doc::text("[")
                        //     .append(Doc::intersperse(
                        //         elems.iter().map(|elem| self.emit_rvalue(env, elem)),
                        //         Doc::text(";").append(Doc::line()),
                        //     ))
                        //     .append(Doc::text("]"))
                        //     .group()
                        //     .nest(2),
                        elems.iter().rev().fold(
                            unaryfn(Doc::text("Nil"), elem_ty_arg.clone()),
                            |doc, elem| {
                                Doc::text("(Cons")
                                    .append(Doc::line())
                                    .append(elem_ty_arg.clone())
                                    .group()
                                    .append(Doc::line())
                                    .append(self.emit_rvalue(env, elem))
                                    .group()
                                    .nest(2)
                                    .append(Doc::line())
                                    .append(doc)
                                    .append(")")
                            },
                        ),
                        Doc::text(elems.len().to_string()),
                    ])
                }
                ExprT::Malloc(ty) => parens(
                    Doc::text("Pulse.Lib.C.Ref.alloc_ref")
                        .append(Doc::line())
                        .append(Doc::text("#"))
                        .append(self.emit_type(env, ty))
                        .append(Doc::line())
                        .append("()"),
                ),
                ExprT::Calloc(ty) => parens(
                    Doc::text("Pulse.Lib.C.Ref.calloc_ref")
                        .append(Doc::line())
                        .append(Doc::text("#"))
                        .append(self.emit_type(env, ty))
                        .append(Doc::line())
                        .append("()"),
                ),
                ExprT::MallocArray(ty, count) => parens(
                    Doc::text("Pulse.Lib.C.Array.alloc_array")
                        .append(Doc::line())
                        .append(Doc::text("#"))
                        .append(self.emit_type(env, ty))
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, count)),
                ),
                ExprT::CallocArray(ty, count) => parens(
                    Doc::text("Pulse.Lib.C.Array.calloc_array")
                        .append(Doc::line())
                        .append(Doc::text("#"))
                        .append(self.emit_type(env, ty))
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, count)),
                ),
                ExprT::MallocFlex(ty, count) | ExprT::CallocFlex(ty, count) => {
                    let flex_kind = if matches!(&v.val, ExprT::MallocFlex(..)) {
                        "malloc_flex"
                    } else {
                        "calloc_flex"
                    };
                    let resolved = env.vtype_whnf(ty.clone().into());
                    match &resolved.val {
                        TypeT::TypeRef(TypeRefKind::Struct(struct_name)) => parens(
                            self.emit_name(Name::StructAuxFn(
                                struct_name.val.clone(),
                                flex_kind.into(),
                            ))
                            .append(Doc::line())
                            .append(self.emit_rvalue(env, count)),
                        ),
                        _ => {
                            self.report(
                                "flexible-array-member allocation of a non-struct type".to_string(),
                                &ty.loc,
                            );
                            Doc::text("()")
                        }
                    }
                }
                ExprT::Memset(_, ptr, value, count) => parens(
                    Doc::text("Pulse.Lib.C.Array.memset")
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, ptr))
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, value))
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, count))
                        .group()
                        .nest(2),
                ),
                ExprT::MemsetZero(_, ptr) => parens(
                    self.emit_rvalue(env, ptr)
                        .append(Doc::line())
                        .append(":=")
                        .append(Doc::line())
                        .append("zero_default")
                        .group()
                        .nest(2),
                ),
                ExprT::Free(val) => {
                    let is_array = env
                        .infer_expr(val)
                        .map(|ty| {
                            matches!(
                                env.vtype_whnf(ty).val,
                                TypeT::Pointer(_, PointerKind::Array)
                            )
                        })
                        .unwrap_or(false);
                    let func = if is_array {
                        "Pulse.Lib.C.Array.free_array"
                    } else {
                        "Pulse.Lib.C.Ref.free_ref"
                    };
                    parens(
                        Doc::text(func)
                            .append(Doc::line())
                            .append(self.emit_rvalue(env, val)),
                    )
                }
                ExprT::ContainerOf(ptr, struct_ty, field) => {
                    let resolved = env.vtype_whnf(struct_ty.clone().into());
                    match &resolved.val {
                        TypeT::TypeRef(TypeRefKind::Struct(struct_name)) => {
                            let container = self.emit_name(Name::StructContainerFn(
                                struct_name.val.clone(),
                                field.val.clone(),
                            ));
                            parens(unaryfn(container, self.emit_rvalue(env, ptr)))
                        }
                        _ => {
                            self.report(
                                format!("_container_of expects a struct type, got {}", struct_ty),
                                &struct_ty.loc,
                            );
                            Doc::text("(admit())")
                        }
                    }
                }
                ExprT::PreIncr(val)
                | ExprT::PostIncr(val)
                | ExprT::PreDecr(val)
                | ExprT::PostDecr(val) => {
                    // Check if this is pointer arithmetic (arrayptr++/--)
                    let val_ty = env.infer_expr(val).ok().map(|t| env.vtype_whnf(t));
                    let is_ptr = val_ty.as_ref().is_some_and(|t| {
                        matches!(
                            t.val,
                            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr)
                        )
                    });
                    if is_ptr {
                        let is_incr = matches!(&v.val, ExprT::PreIncr(_) | ExprT::PostIncr(_));
                        let is_pre = matches!(&v.val, ExprT::PreIncr(_) | ExprT::PreDecr(_));
                        let prefix = if is_pre { "pre" } else { "post" };
                        let dir = if is_incr { "incr" } else { "decr" };
                        parens(
                            Doc::text(format!("Pulse.Lib.C.Array.arrayptr_{}_{}", prefix, dir))
                                .append(Doc::line())
                                .append(self.emit_lvalue(env, val)),
                        )
                    } else {
                        let prefix = match &v.val {
                            ExprT::PreIncr(_) => "pluspluspre",
                            ExprT::PostIncr(_) => "pluspluspost",
                            ExprT::PreDecr(_) => "minusminuspre",
                            ExprT::PostDecr(_) => "minusminuspost",
                            _ => unreachable!(),
                        };
                        let suffix = val_ty.and_then(|ty| match &ty.val {
                            TypeT::Int { signed, width } => {
                                get_int_mod(signed, width).map(|s| s.to_lowercase())
                            }
                            TypeT::Float { width: 32 } => Some("float32".to_string()),
                            TypeT::Float { width: 64 } => Some("float64".to_string()),
                            TypeT::SizeT => Some("sizet".to_string()),
                            TypeT::PtrdiffT => Some("ptrdifft".to_string()),
                            _ => None,
                        });
                        let suffix = suffix.unwrap_or_else(|| "unknown".to_string());
                        parens(
                            Doc::text(format!("Pulse.Lib.C.UnaryOps.{}_{}", prefix, suffix))
                                .append(Doc::line())
                                .append(self.emit_lvalue(env, val)),
                        )
                    }
                }
                ExprT::Cond(cond, then_expr, else_expr) => parens(
                    Doc::text("if")
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, cond))
                        .group()
                        .append(Doc::line())
                        .append("then")
                        .append(Doc::line().append(self.emit_rvalue(env, then_expr)).nest(2))
                        .append(Doc::line())
                        .append("else")
                        .append(Doc::line().append(self.emit_rvalue(env, else_expr)).nest(2)),
                ),
                ExprT::AssignExpr(lhs, rhs) => {
                    if let ExprT::Index(arr, idx) = &lhs.val {
                        let is_arrayptr = env
                            .infer_expr(arr)
                            .map(|ty| {
                                matches!(
                                    env.vtype_whnf(ty).val,
                                    TypeT::Pointer(_, PointerKind::ArrayPtr)
                                )
                            })
                            .unwrap_or(false);
                        let fn_name = if is_arrayptr {
                            "arrayptr_assign_ret"
                        } else {
                            "array_assign_ret"
                        };
                        let arr_doc = match self.emit_expr(env, arr) {
                            ExprKind::ArrayLValue(arr_doc) => arr_doc,
                            arr_doc => arr_doc.to_rvalue(),
                        };
                        naryfn([
                            Doc::text(fn_name),
                            arr_doc,
                            self.emit_rvalue(env, idx),
                            self.emit_rvalue(env, rhs),
                        ])
                    } else if let ExprT::Deref(inner) = &lhs.val {
                        let write_fn = env
                            .infer_expr(inner)
                            .map(|ty| match env.vtype_whnf(ty).val {
                                TypeT::Pointer(_, PointerKind::Array) => Some("array_assign_ret"),
                                TypeT::Pointer(_, PointerKind::ArrayPtr) => {
                                    Some("arrayptr_assign_ret")
                                }
                                _ => None,
                            })
                            .unwrap_or(None);
                        if let Some(write_fn) = write_fn {
                            naryfn([
                                Doc::text(write_fn),
                                self.emit_rvalue(env, inner),
                                Doc::text("0sz"),
                                self.emit_rvalue(env, rhs),
                            ])
                        } else {
                            naryfn([
                                Doc::text("assign_ret"),
                                self.emit_lvalue(env, lhs),
                                self.emit_rvalue(env, rhs),
                            ])
                        }
                    } else {
                        naryfn([
                            Doc::text("assign_ret"),
                            self.emit_lvalue(env, lhs),
                            self.emit_rvalue(env, rhs),
                        ])
                    }
                }
                ExprT::SizeOf(ty) => {
                    // `emit_type` renders a fixed-size array `T[N]` as
                    // `full_array_lspec T N`, so `sizeof(T[N])` becomes
                    // `c_sizeof (full_array_lspec T N)` and its length
                    // participates in the size (see the `c_sizeof_array` axiom).
                    // Other types size opaquely.
                    unaryfn(
                        Doc::text("Pulse.Lib.C.Sizeof.c_sizeof"),
                        self.emit_type(env, ty),
                    )
                }
                ExprT::AlignOf(ty) => {
                    let ty_doc = match &ty.val {
                        TypeT::FixedArray(elem, _) => {
                            unaryfn(Doc::text("array"), self.emit_type(env, elem))
                        }
                        _ => self.emit_type(env, ty),
                    };
                    unaryfn(Doc::text("Pulse.Lib.C.Sizeof.c_alignof"), ty_doc)
                }
            }
        })
    }

    fn emit_stmt(&mut self, env: &Env, stmt: &Stmt) -> Doc {
        annotated(stmt, || {
            match &stmt.val {
                StmtT::Call(v) => {
                    // A bare call statement whose value is not unit/void must
                    // explicitly discard its result, since Pulse requires the
                    // statement to have type `unit`.
                    let discard_lead = if env
                        .infer_expr(v)
                        .map(|t| !matches!(env.vtype_whnf(t).val, TypeT::Void))
                        .unwrap_or(false)
                    {
                        Doc::text("let _ = ")
                    } else {
                        Doc::nil()
                    };
                    if let ExprT::FnCall(f, args) = &v.val
                        && let Some(fn_decl) = env.lookup_fn(f)
                    {
                        let mut prelude = Vec::new();
                        let mut emitted_args = Vec::new();
                        for (i, arg) in args.iter().enumerate() {
                            let callee_expects_array = fn_decl.args.get(i).is_some_and(|fn_arg| {
                                matches!(
                                    env.vtype_whnf(fn_arg.ty.clone().into()).val,
                                    TypeT::Pointer(_, PointerKind::Array)
                                )
                            });
                            // `&a[i]` passed into a plain `int *` param (a Pulse
                            // `ref`) where `a` is a real `_array`: borrow cell `i`
                            // out of the array with `array_borrow_cell`. The
                            // borrow is emitted as a call prelude and the fresh
                            // binding passed in place of the address-of
                            // expression. (The name is not strictly required --
                            // an inline `f (array_borrow_cell a i)` would be
                            // A-normalized by Pulse to the same binding.) The
                            // returning side is invoked manually by the user via
                            // inline Pulse.
                            //
                            // The cell is handed out as `pts_to_maybe_uninit`
                            // carrying its current optional value. At the call the
                            // maybe-cell adapts to whatever the callee expects via
                            // the `[@@pulse_intro]` coercions -- `reveal_maybe` for
                            // a readable `pts_to` (when the cell is known `Some`),
                            // `forget_maybe` for a write-only `pts_to_uninit`
                            // (`_out`) -- so the call itself typechecks with no
                            // ghost step. PAL does NOT, however, emit the matching
                            // return: after the call the (now written) cell is left
                            // carved out of the array, so a function whose
                            // postcondition owns the *whole* array cannot
                            // re-establish it and F* reports leftover resources.
                            // Handing a cell to such a function therefore requires
                            // borrowing into a local (`T* p = &a[i];`) and giving
                            // the cell back explicitly (`intro_maybe_some` + the
                            // index-inferring `array_return_cell`); the direct
                            // `f(&a[i])` form carries the borrow one way only.
                            let borrow_cell = match &arg.val {
                                ExprT::Ref(inner) => match &inner.val {
                                    ExprT::Index(arr, idx) => {
                                        let param = fn_decl.args.get(i);
                                        let param_is_ref = param.is_some_and(|fn_arg| {
                                            matches!(
                                                env.vtype_whnf(fn_arg.ty.clone().into()).val,
                                                TypeT::Pointer(_, PointerKind::Ref)
                                            )
                                        });
                                        let arr_is_array = env
                                            .infer_expr(arr)
                                            .ok()
                                            .map(|t| env.vtype_whnf(t))
                                            .is_some_and(|t| {
                                                matches!(
                                                    &t.val,
                                                    TypeT::Pointer(_, PointerKind::Array)
                                                )
                                            });
                                        if param_is_ref && arr_is_array {
                                            Some((arr.clone(), idx.clone()))
                                        } else {
                                            None
                                        }
                                    }
                                    _ => None,
                                },
                                _ => None,
                            };
                            let array_init = match &arg.val {
                                ExprT::ArrayInit {
                                    elem_ty, is_static, ..
                                } => Some((elem_ty, arg, *is_static)),
                                ExprT::Cast(inner, _)
                                    if matches!(inner.val, ExprT::ArrayInit { .. }) =>
                                {
                                    match &inner.val {
                                        ExprT::ArrayInit {
                                            elem_ty, is_static, ..
                                        } => Some((elem_ty, inner, *is_static)),
                                        _ => None,
                                    }
                                }
                                _ => None,
                            };
                            if let Some((arr, idx)) = borrow_cell {
                                let tmp = self.fresh_tmp("borrow");
                                let arr_doc = self.emit_rvalue(env, &arr);
                                let idx_doc = self.emit_rvalue(env, &idx);
                                let borrow = Doc::text("let ")
                                    .append(tmp.clone())
                                    .append(Doc::text(" ="))
                                    .append(Doc::line())
                                    .append(naryfn([
                                        Doc::text("array_borrow_cell"),
                                        arr_doc,
                                        idx_doc,
                                    ]))
                                    .append(";")
                                    .nest(2)
                                    .group();
                                prelude.push(borrow);
                                emitted_args.push(tmp);
                            } else if let Some((elem_ty, spec_arg, is_static)) = array_init
                                && (callee_expects_array || !is_static)
                            {
                                let tmp = self.fresh_tmp("arraylit");
                                let elem_ty_doc = self.emit_type(env, elem_ty);
                                let spec_doc = self.emit_rvalue(env, spec_arg);
                                let alloc = Doc::text("let ")
                                    .append(tmp.clone())
                                    .append(Doc::text(" ="))
                                    .append(Doc::line())
                                    .append(naryfn([
                                        Doc::text("stack_alloc_array_full"),
                                        Doc::text("#").append(elem_ty_doc),
                                        spec_doc.clone(),
                                    ]))
                                    .append(";")
                                    .nest(2)
                                    .group();
                                let defer = Doc::text("defer ")
                                    .append(naryfn([
                                        Doc::text("array_pts_to_full"),
                                        tmp.clone(),
                                        Doc::text("1.0R"),
                                        spec_doc,
                                    ]))
                                    .nest(2)
                                    .group()
                                    .append(Doc::line())
                                    .append(Doc::text("{ stack_free_array_full _ }"))
                                    .append(";")
                                    .nest(2)
                                    .group();
                                prelude.push(alloc);
                                prelude.push(defer);
                                emitted_args.push(if callee_expects_array {
                                    tmp
                                } else {
                                    unaryfn(Doc::text("Pulse.Lib.C.Array.array_to_ref"), tmp)
                                });
                            } else {
                                emitted_args.push(self.emit_rvalue(env, arg));
                            }
                        }
                        if !prelude.is_empty() {
                            let call_doc = Doc::concat(
                                prelude.into_iter().map(|doc| doc.append(Doc::hardline())),
                            )
                            .append(
                                discard_lead
                                    .append(parens(
                                        self.emit_name(Name::Fn(f.val.clone()))
                                            .append(Doc::concat(
                                                emitted_args
                                                    .into_iter()
                                                    .map(|arg| Doc::line().append(arg)),
                                            ))
                                            .nest(2),
                                    ))
                                    .append(";")
                                    .nest(2)
                                    .group(),
                            );
                            return call_doc;
                        }
                    }
                    discard_lead
                        .append(self.emit_rvalue(env, v))
                        .append(";")
                        .nest(2)
                        .group()
                }
                StmtT::Decl(x, ty) => {
                    if let TypeT::FixedArray(elem_ty, length) = &ty.val {
                        // Fixed-size array declaration: emit stack_alloc_array + defer
                        let x_doc = self.emit_name(Name::Var(x.val.clone()));
                        let elem_type_doc = self.emit_type(env, elem_ty);
                        let size_doc = Doc::text(format!("{}sz", length));
                        let alloc = Doc::text("let ")
                            .append(x_doc.clone())
                            .append(Doc::text(" ="))
                            .append(Doc::line())
                            .append(naryfn([
                                Doc::text("stack_alloc_array"),
                                Doc::text("#").append(elem_type_doc),
                                size_doc,
                            ]))
                            .append(";")
                            .nest(2)
                            .group();
                        let defer = Doc::text("defer ")
                            .append(unaryfn(Doc::text("array_pts_to_uninit'"), x_doc.clone()))
                            .nest(2)
                            .group()
                            .append(Doc::line())
                            .append(Doc::text("{ stack_free_array _ }"))
                            .append(";")
                            .nest(2)
                            .group();
                        let redecl = Doc::text("let mut ")
                            .append(x_doc.clone())
                            .append(" =")
                            .append(Doc::line())
                            .append(x_doc)
                            .append(";")
                            .nest(2)
                            .group();
                        alloc
                            .append(Doc::hardline())
                            .append(defer)
                            .append(Doc::hardline())
                            .append(redecl)
                    } else {
                        let x = self.emit_name(Name::Var(x.val.clone()));
                        (Doc::text("let mut ").append(x).append(" :"))
                            .append(Doc::line())
                            .append(self.emit_type(env, ty))
                            .append(";")
                            .nest(2)
                            .group()
                    }
                }
                StmtT::Let(x, ty, value) => Doc::text("let ")
                    .append(self.emit_name(Name::Var(x.val.clone())))
                    .append(" :")
                    .append(Doc::line())
                    .append(self.emit_type(env, ty))
                    .append(Doc::line())
                    .append("=")
                    .group()
                    .append(Doc::line().append(self.emit_rvalue(env, value)).nest(2))
                    .append(";")
                    .nest(2)
                    .group(),
                StmtT::DeclStackArray {
                    name,
                    elem_type,
                    size,
                } => {
                    let x = self.emit_name(Name::Var(name.val.clone()));
                    let size_doc = self.emit_rvalue(env, size);
                    let elem_type_doc = self.emit_type(env, elem_type);
                    // let var_arr = stack_alloc_array #Int32.t 10sz;
                    let alloc = Doc::text("let ")
                        .append(x.clone())
                        .append(Doc::text(" ="))
                        .append(Doc::line())
                        .append(naryfn([
                            Doc::text("stack_alloc_array"),
                            Doc::text("#").append(elem_type_doc),
                            size_doc,
                        ]))
                        .append(";")
                        .nest(2)
                        .group();
                    // defer array_pts_to_uninit' var_arr {stack_free_array _};
                    let defer = Doc::text("defer ")
                        .append(unaryfn(Doc::text("array_pts_to_uninit'"), x.clone()))
                        .nest(2)
                        .group()
                        .append(Doc::line())
                        .append(Doc::text("{ stack_free_array _ }"))
                        .append(";")
                        .nest(2)
                        .group();
                    // let mut arr = arr;  (redeclare as ref for lvalue convention)
                    let redecl = Doc::text("let mut ")
                        .append(x.clone())
                        .append(" =")
                        .append(Doc::line())
                        .append(x)
                        .append(";")
                        .nest(2)
                        .group();
                    alloc
                        .append(Doc::hardline())
                        .append(defer)
                        .append(Doc::hardline())
                        .append(redecl)
                }
                StmtT::Assign(x, t) => {
                    // Function-pointer store (`fp = add`, `fp = other`, `fp = 0`,
                    // ...) needs no special handling: the ref keeps ordinary
                    // `pts_to` ownership. A concrete `fp = add` stores the
                    // `of_fn` value (emitted by `emit_rvalue`'s `FnRef` arm), and
                    // the `of_fn_valid` ghost step later recovers validity from
                    // that stored value. So fnptr stores fall through to the
                    // generic store below — no `intro`/`elim`/`copy` `valid_ptr`,
                    // no tracking.
                    // `x = &a[i]` where `a` is an `_array` and `x` is a `ref`
                    // local: borrow cell `i` out of the array as a `ref` and
                    // bind it to `x`. This is the non-argument counterpart of
                    // the call-site cell borrow above: `array_borrow_cell` hands
                    // the cell out as `pts_to_maybe_uninit`, leaving the array
                    // with that cell carved out. The user then adapts the
                    // maybe-cell (e.g. `forget_maybe` to fill an uninitialized
                    // struct field-by-field through `x`) and later returns it to
                    // the array with `array_return_cell`. The borrow call is
                    // stored directly into the (mutable) `ref` local `x`.
                    if let ExprT::Ref(inner) = &t.val
                        && let ExprT::Index(arr, idx) = &inner.val
                        && env
                            .infer_expr(arr)
                            .ok()
                            .map(|ty| env.vtype_whnf(ty))
                            .is_some_and(|ty| {
                                matches!(ty.val, TypeT::Pointer(_, PointerKind::Array))
                            })
                        && env
                            .infer_expr(x)
                            .ok()
                            .map(|ty| env.vtype_whnf(ty))
                            .is_some_and(|ty| matches!(ty.val, TypeT::Pointer(_, PointerKind::Ref)))
                    {
                        let arr_doc = self.emit_rvalue(env, arr);
                        let idx_doc = self.emit_rvalue(env, idx);
                        return self
                            .emit_lvalue(env, x)
                            .append(Doc::line())
                            .append(":=")
                            .group()
                            .append(Doc::line())
                            .append(naryfn([Doc::text("array_borrow_cell"), arr_doc, idx_doc]))
                            .append(";")
                            .group()
                            .nest(2);
                    }
                    // `x = <arrayptr>` where `x` is a `ref` local: borrow the
                    // cell the arrayptr points at out of its (still-live) parent
                    // array as a `ref` and bind it to `x`. This is the arrayptr
                    // counterpart of the `&a[i]` borrow-to-local above -- e.g. a
                    // helper *returns* an arrayptr and the caller stores it in a
                    // plain-pointer local before writing through it. The
                    // elaborator leaves the plain-pointer local as a `ref` and
                    // inserts an `ArrayPtr -> Ref` cast on the initializer; the
                    // arrayptr is the cast's operand (often an inlined,
                    // anonymous call result). `arrayptr_borrow_cell` hands the
                    // cell out as `pts_to_maybe_uninit`; the user then adapts it
                    // (e.g. `forget_maybe` to fill an uninitialized struct
                    // field-by-field) and later returns it to the parent array
                    // with `array_return_cell` -- whose cell index is inferred,
                    // so it reconciles the borrowed cell's symbolic arrayptr
                    // offset even though no named arrayptr handle survives the
                    // inlined borrow. PAL never guesses the cell's
                    // initialization state.
                    if let ExprT::Cast(inner, _) = &t.val
                        && env
                            .infer_expr(inner)
                            .ok()
                            .map(|ty| env.vtype_whnf(ty))
                            .is_some_and(|ty| {
                                matches!(ty.val, TypeT::Pointer(_, PointerKind::ArrayPtr))
                            })
                        && env
                            .infer_expr(x)
                            .ok()
                            .map(|ty| env.vtype_whnf(ty))
                            .is_some_and(|ty| matches!(ty.val, TypeT::Pointer(_, PointerKind::Ref)))
                    {
                        let ap_doc = self.emit_rvalue(env, inner);
                        return self
                            .emit_lvalue(env, x)
                            .append(Doc::line())
                            .append(":=")
                            .group()
                            .append(Doc::line())
                            .append(naryfn([Doc::text("arrayptr_borrow_cell"), ap_doc]))
                            .append(";")
                            .group()
                            .nest(2);
                    }
                    // a[i].field = val → array_update / arrayptr_update
                    // (*p).field = val → array_update / arrayptr_update at index 0
                    //   (the `p->field` form, where `p` is an array/arrayptr)
                    if let ExprT::Member(base, fld) = &x.val {
                        // Resolve the array/arrayptr being projected and the element index.
                        // The deref form only applies to array/arrayptr pointers; plain
                        // struct pointers fall through to the generic lvalue path below.
                        let arr_and_idx: Option<(&Rc<Expr>, Option<&Rc<Expr>>)> = match &base.val {
                            ExprT::Index(arr, idx) => Some((arr, Some(idx))),
                            ExprT::Deref(ptr) => Some((ptr, None)),
                            _ => None,
                        };
                        if let Some((arr, idx)) = arr_and_idx {
                            let arr_ty = env.infer_expr(arr).ok().map(|ty| env.vtype_whnf(ty));
                            let is_arrayptr = arr_ty
                                .as_ref()
                                .map(|ty| {
                                    matches!(ty.val, TypeT::Pointer(_, PointerKind::ArrayPtr))
                                })
                                .unwrap_or(false);
                            let is_array = arr_ty
                                .as_ref()
                                .map(|ty| matches!(ty.val, TypeT::Pointer(_, PointerKind::Array)))
                                .unwrap_or(false);
                            let applies = idx.is_some() || is_array || is_arrayptr;
                            // Check that the element type is a struct
                            if applies
                                && let Some(struct_name) =
                                    env.infer_expr(base).ok().and_then(|ty| {
                                        let ty = env.vtype_whnf(ty);
                                        match &ty.val {
                                            TypeT::TypeRef(TypeRefKind::Struct(s)) => {
                                                Some(s.val.clone())
                                            }
                                            _ => None,
                                        }
                                    })
                            {
                                let fn_name = if is_arrayptr {
                                    "arrayptr_update"
                                } else {
                                    "array_update"
                                };
                                let arr_doc = match self.emit_expr(env, arr) {
                                    ExprKind::ArrayLValue(arr_doc) => arr_doc,
                                    arr_doc => arr_doc.to_rvalue(),
                                };
                                let idx_doc = match idx {
                                    Some(idx) => self.emit_rvalue(env, idx),
                                    None => Doc::text("0sz"),
                                };
                                let field_name = self.emit_name(Name::StructDirectFieldName(
                                    struct_name,
                                    fld.val.clone(),
                                ));
                                let upd_fn = Doc::text("(fun __v __y -> { __v with ")
                                    .append(field_name)
                                    .append(Doc::text(" = __y })"));
                                return naryfn([
                                    Doc::text(fn_name),
                                    arr_doc,
                                    idx_doc,
                                    upd_fn,
                                    self.emit_rvalue(env, t),
                                ])
                                .append(";")
                                .nest(2)
                                .group();
                            }
                        }
                    }
                    if let ExprT::Index(arr, idx) = &x.val {
                        let is_arrayptr = env
                            .infer_expr(arr)
                            .map(|ty| {
                                matches!(
                                    env.vtype_whnf(ty).val,
                                    TypeT::Pointer(_, PointerKind::ArrayPtr)
                                )
                            })
                            .unwrap_or(false);
                        let fn_name = if is_arrayptr {
                            "arrayptr_write"
                        } else {
                            "array_write"
                        };
                        let arr_doc = match self.emit_expr(env, arr) {
                            ExprKind::ArrayLValue(arr_doc) => arr_doc,
                            arr_doc => arr_doc.to_rvalue(),
                        };
                        let idx_doc = self.emit_rvalue(env, idx);
                        let val_doc = self.emit_rvalue(env, t);
                        naryfn([Doc::text(fn_name), arr_doc, idx_doc, val_doc])
                            .append(";")
                            .nest(2)
                            .group()
                    } else if let ExprT::Deref(inner) = &x.val {
                        // *array     = val → array_write    p 0sz val
                        // *arrayptr  = val → arrayptr_write p 0sz val
                        let write_fn = env
                            .infer_expr(inner)
                            .map(|ty| match env.vtype_whnf(ty).val {
                                TypeT::Pointer(_, PointerKind::Array) => Some("array_write"),
                                TypeT::Pointer(_, PointerKind::ArrayPtr) => Some("arrayptr_write"),
                                _ => None,
                            })
                            .unwrap_or(None);
                        if let Some(write_fn) = write_fn {
                            naryfn([
                                Doc::text(write_fn),
                                self.emit_rvalue(env, inner),
                                Doc::text("0sz"),
                                self.emit_rvalue(env, t),
                            ])
                            .append(";")
                            .nest(2)
                            .group()
                        } else {
                            self.emit_lvalue(env, x)
                                .append(Doc::line())
                                .append(":=")
                                .group()
                                .append(Doc::line())
                                .append(self.emit_rvalue(env, t))
                                .append(";")
                                .group()
                                .nest(2)
                        }
                    } else if let ExprT::Member(base, fld) = &x.val {
                        // Check if base is a union type — if so, emit x := Ctor val
                        if let Ok(base_ty) = env.infer_expr(base) {
                            let base_ty = env.vtype_whnf(base_ty);
                            if let TypeT::TypeRef(TypeRefKind::Union(union_name)) = &base_ty.val {
                                let ctor = self.emit_name(Name::UnionFieldConstructor(
                                    union_name.val.clone(),
                                    fld.val.clone(),
                                ));
                                return self
                                    .emit_lvalue(env, base)
                                    .append(Doc::line())
                                    .append(":=")
                                    .group()
                                    .append(Doc::line())
                                    .append(unaryfn(ctor, self.emit_rvalue(env, t)))
                                    .append(";")
                                    .group()
                                    .nest(2);
                            }
                        }
                        // Fall through to normal assignment for struct members.
                        // A *partial* sub-field write into a union arm
                        // (`u->arm.field = v`) requires the arm be active; this
                        // is now the user's responsibility via
                        // `_ghost_stmt($activate(union U::arm) $(u))`.
                        // For an unsigned bit-field, mask the RHS to its width so
                        // the stored value satisfies the cell's `< pow2 N`
                        // refinement (C unsigned modular truncation on write).
                        let rhs = match self.bitfield_member_mask(env, x) {
                            Some((width, mask_fn)) => naryfn([
                                Doc::text(mask_fn),
                                Doc::text(width.to_string()),
                                self.emit_rvalue(env, t),
                            ]),
                            None => self.emit_rvalue(env, t),
                        };
                        self.emit_lvalue(env, x)
                            .append(Doc::line())
                            .append(":=")
                            .group()
                            .append(Doc::line())
                            .append(rhs)
                            .append(";")
                            .group()
                            .nest(2)
                    } else {
                        self.emit_lvalue(env, x)
                            .append(Doc::line())
                            .append(":=")
                            .group()
                            .append(Doc::line())
                            .append(self.emit_rvalue(env, t))
                            .append(";")
                            .group()
                            .nest(2)
                    }
                }
                StmtT::If {
                    cond,
                    then_branch,
                    else_branch,
                    ensures,
                } => {
                    let cond_doc = parens(self.emit_rvalue(env, cond));
                    let ensures_doc = Doc::concat(ensures.iter().map(|e| {
                        Doc::line()
                            .append("ensures ")
                            .append(self.emit_rvalue(env, e))
                            .group()
                            .nest(2)
                    }));
                    let then_doc = self.emit_block(env, then_branch);
                    let else_doc = self.emit_block(env, else_branch);
                    Doc::text("if ")
                        .append(cond_doc)
                        .nest(2)
                        .append(ensures_doc)
                        .append(" ")
                        .append(then_doc)
                        .append(" else ")
                        .append(else_doc)
                        .append(";")
                        .group()
                }
                StmtT::Match {
                    scrutinee,
                    branches,
                    default_branch,
                    ensures,
                } => {
                    let mut branch_docs = Vec::new();
                    for branch in &**branches {
                        for pattern in &*branch.patterns {
                            branch_docs.push(
                                Doc::line()
                                    .append(self.emit_pattern(env, pattern))
                                    .append(" -> ")
                                    .append(self.emit_block(env, &branch.body))
                                    .nest(2),
                            );
                        }
                    }
                    let match_doc = Doc::text("match ")
                        .append(parens(self.emit_rvalue(env, scrutinee)))
                        .append(" {")
                        .append(Doc::concat(branch_docs))
                        .append(Doc::line())
                        .append("_ -> ")
                        .append(self.emit_block(env, default_branch))
                        .nest(2)
                        .append(Doc::line())
                        .append("};")
                        .group();
                    if ensures.is_empty() {
                        match_doc
                    } else {
                        // A forward label fixes the join postcondition while
                        // preserving the ambient stt/stt_div effect.
                        let mut doc = block(Doc::hardline().append(match_doc));
                        for e in ensures.iter() {
                            doc = doc
                                .append(Doc::hardline())
                                .append("ensures ")
                                .append(self.emit_rvalue(env, e));
                        }
                        doc.append(Doc::hardline())
                            .append("label ")
                            .append(self.fresh_tmp("match_join"))
                            .append(":;")
                    }
                }
                StmtT::While {
                    cond,
                    inv,
                    requires,
                    ensures,
                    body,
                } => {
                    let head = Doc::text("while ")
                        .append(parens(self.emit_rvalue(env, cond)))
                        .append(Doc::line())
                        .append(Doc::concat(inv.iter().map(|inv| {
                            Doc::text("invariant ")
                                .append(self.emit_rvalue(env, inv))
                                .group()
                                .nest(2)
                                .append(Doc::line())
                        })))
                        .append(Doc::concat(requires.iter().map(|r| {
                            Doc::text("requires ")
                                .append(self.emit_rvalue(env, r))
                                .group()
                                .nest(2)
                                .append(Doc::line())
                        })))
                        .append(Doc::concat(ensures.iter().map(|e| {
                            Doc::text("ensures ")
                                .append(self.emit_rvalue(env, e))
                                .group()
                                .nest(2)
                                .append(Doc::line())
                        })));
                    let body_doc = self.emit_block(env, body);
                    head.nest(2).append(body_doc).append(";").group()
                }
                StmtT::Break => Doc::text("break;"),
                StmtT::Continue => Doc::text("continue;"),
                StmtT::Return(Some(t)) => Doc::text("return")
                    .append(Doc::line())
                    .append(self.emit_rvalue(env, t))
                    .append(";")
                    .group()
                    .nest(2),
                StmtT::Return(None) => Doc::text("return;"),
                // `_assert(false)` is a claim that control never reaches this
                // point, not a proposition to carry forward. Pulse spells that
                // `unreachable ()`, whose postcondition is `pure False`, so the
                // branch absorbs whatever the join needs instead of having to
                // agree with its siblings' resources. Asserting `with_pure
                // False` would instead leave the branch's own footprint in the
                // join and make an unreachable arm the reason a proof fails.
                StmtT::Assert(v) if is_statically_false(v) => Doc::text("unreachable ();"),
                StmtT::Assert(v) => Doc::text("assert")
                    .append(Doc::line())
                    .append(self.emit_rvalue(env, v))
                    .append(";")
                    .group()
                    .nest(2),
                StmtT::GhostStmt(code) => {
                    let env = &mut env.clone();
                    self.emit_inline_pulse_tokens(env, code).append(";")
                }
                StmtT::Goto(label) => Doc::text("goto ")
                    .append(self.emit_name(Name::Var(label.val.clone())))
                    .append(";"),
                StmtT::Label { .. } => Doc::text("(* unrestructured label *)"),
                StmtT::GotoBlock {
                    body,
                    label,
                    ensures,
                } => {
                    let mut doc = block(self.emit_stmts(env, body));
                    for e in ensures.iter() {
                        doc = doc
                            .append(Doc::hardline())
                            .append("ensures ")
                            .append(self.emit_rvalue(env, e));
                    }
                    doc.append(Doc::hardline())
                        .append("label ")
                        .append(self.emit_name(Name::Var(label.val.clone())))
                        .append(":;")
                }
                StmtT::Error => Doc::text("(admit());"),
            }
        })
    }
} // impl Emitter (group B)

fn block(stmts: Doc) -> Doc {
    Doc::text("{")
        .append(stmts.nest(2))
        .append(Doc::hardline())
        .append(Doc::text("}"))
        .group()
}

impl<'a> Emitter<'a> {
    fn emit_stmts(&mut self, env: &Env, stmts: &Vec<Rc<Stmt>>) -> Doc {
        let mut env = env.clone();
        let mut doc = Doc::nil();
        let mut idx = 0;
        while idx < stmts.len() {
            let stmt = &stmts[idx];
            // `return e;` immediately followed by ghost statement(s) needs a
            // rewrite: the ghosts must run live, with access to the returned
            // value. Emit `let <ret> = e; <ghosts>; return <ret>;`. Statements
            // after this return are unreachable, so we stop emitting here.
            // Function-pointer locals need no scope-exit unwrapping: they keep
            // ordinary `pts_to` ownership and are auto-released.
            let followed_by_ghost =
                idx + 1 < stmts.len() && matches!(stmts[idx + 1].val, StmtT::GhostStmt(_));
            if let StmtT::Return(Some(t)) = &stmt.val
                && followed_by_ghost
            {
                let ret_doc = self.emit_rvalue(&env, t);
                let ret_name = self.emit_name(Name::Var(Rc::from("return")));
                doc = doc.append(
                    Doc::line().append(Doc::group(
                        Doc::text("let ")
                            .append(ret_name.clone())
                            .append(" = ")
                            .append(ret_doc)
                            .append(";"),
                    )),
                );
                // Emit the consecutive ghost statements following the return.
                idx += 1;
                while idx < stmts.len() && matches!(stmts[idx].val, StmtT::GhostStmt(_)) {
                    doc = doc.append(Doc::line().append(self.emit_stmt(&env, &stmts[idx])));
                    env.push_stmt(&stmts[idx]);
                    idx += 1;
                }
                doc = doc.append(
                    Doc::line().append(
                        Doc::text("return")
                            .append(Doc::line())
                            .append(ret_name)
                            .append(";")
                            .group()
                            .nest(2),
                    ),
                );
                break;
            }
            doc = doc.append(Doc::line().append(self.emit_stmt(&env, stmt)));
            env.push_stmt(stmt);
            idx += 1;
        }
        doc
    }

    fn emit_block(&mut self, env: &Env, stmts: &Vec<Rc<Stmt>>) -> Doc {
        if stmts.is_empty() {
            return Doc::text("{}");
        }
        block(self.emit_stmts(env, stmts))
    }
} // impl Emitter (group C)

fn mk_let(n: Doc, args: &[Doc], ty: Doc, body: Doc) -> Doc {
    mk_let_rec(false, n, args, ty, body)
}

fn mk_let_rec(is_rec: bool, n: Doc, args: &[Doc], ty: Doc, body: Doc) -> Doc {
    let keyword = if is_rec {
        Doc::text("let rec")
    } else {
        Doc::text("let")
    };
    (keyword.append(Doc::line()).append(n))
        .append(
            Doc::concat(args.iter().map(|arg| Doc::line().append(arg.clone())))
                .append(Doc::line().append(":"))
                .nest(2),
        )
        .group()
        .append(Doc::line().append(ty))
        .append(Doc::line().append("="))
        .nest(2)
        .group()
        .append(Doc::line().append(body))
        .group()
        .nest(2)
}

fn mk_instance(n: Doc, args: &[Doc], ty: Doc, body: Doc) -> Doc {
    (Doc::text("instance").append(Doc::line()).append(n))
        .append(
            Doc::concat(args.iter().map(|arg| Doc::line().append(arg.clone())))
                .append(Doc::line().append(":"))
                .nest(2),
        )
        .group()
        .append(Doc::line().append(ty))
        .append(Doc::line().append("="))
        .nest(2)
        .group()
        .append(Doc::line().append(body))
        .group()
        .nest(2)
}

fn mk_eager_unfold_slprop(n: Doc, args: &[Doc], body: Doc) -> Doc {
    (Doc::text("[@@pulse_eager_unfold]")
        .append(Doc::line())
        .append("let")
        .append(Doc::line())
        .append("predicate")
        .group()
        .append(Doc::line())
        .append(n))
    .group()
    .append(
        Doc::concat(args.iter().map(|arg| Doc::line().append(arg.clone())))
            .nest(2)
            .append(Doc::line().append("=").group()),
    )
    .group()
    .nest(2)
    .group()
    .append(Doc::line().append(body))
    .group()
    .nest(2)
}

fn mk_star<I: IntoIterator<Item = Doc>>(ps: I) -> Doc {
    match ps.into_iter().reduce(|accum, p| {
        accum
            .append(Doc::space())
            .append("**")
            .append(Doc::line())
            .append(p)
    }) {
        Some(star) => parens(star),
        None => Doc::text("emp"),
    }
}

fn mk_rvar(n: &Rc<Ident>) -> Rc<Expr> {
    ExprT::Var(n.clone()).with_loc(n.loc.clone())
}

/// Rewrite a flexible-array-member `_refines` predicate (elaborated with the
/// array itself bound to `this` and sibling fields referenced by name) into a
/// struct-relative predicate for use inside the struct predicate: the array
/// `this` becomes `this.<fam_field>` and every sibling field reference `f`
/// becomes `this.<f>`, where `this` is the struct value bound in the predicate.
fn subst_flex_refine_pred(expr: &Expr, fam_field: &Rc<Ident>, this: &Rc<Ident>) -> Rc<Expr> {
    let loc = expr.loc.clone();
    match &expr.val {
        ExprT::Var(x) => {
            let field = if &*x.val == "this" {
                fam_field.clone()
            } else {
                x.clone()
            };
            ExprT::Member(mk_rvar(this), field).with_loc(loc)
        }
        ExprT::VAttr(a, x) => {
            ExprT::VAttr(a.clone(), subst_flex_refine_pred(x, fam_field, this)).with_loc(loc)
        }
        ExprT::BinOp(op, l, r) => ExprT::BinOp(
            *op,
            subst_flex_refine_pred(l, fam_field, this),
            subst_flex_refine_pred(r, fam_field, this),
        )
        .with_loc(loc),
        ExprT::UnOp(op, a) => {
            ExprT::UnOp(*op, subst_flex_refine_pred(a, fam_field, this)).with_loc(loc)
        }
        ExprT::Cast(vv, t) => {
            ExprT::Cast(subst_flex_refine_pred(vv, fam_field, this), t.clone()).with_loc(loc)
        }
        ExprT::Member(x, a) => {
            ExprT::Member(subst_flex_refine_pred(x, fam_field, this), a.clone()).with_loc(loc)
        }
        ExprT::FnCall(f, args) => ExprT::FnCall(
            f.clone(),
            args.iter()
                .map(|a| subst_flex_refine_pred(a, fam_field, this))
                .collect(),
        )
        .with_loc(loc),
        _ => Rc::new(expr.clone()),
    }
}

impl<'a> Emitter<'a> {
    fn emit_typedef(
        &mut self,
        env: &Env,
        decl @ TypeDefn {
            name,
            body,
            is_pointer_view: _,
        }: &TypeDefn,
    ) -> Doc {
        let env = &mut env.clone();
        env.push_typedef(decl.clone());

        let k = &TypeRefKind::Typedef(name.clone());
        let t = self.emit_name(Name::TypeRef(k.into()));
        // The unfold here is important to trigger the loop detection in the Pulse prover
        let ty_decl = Doc::text("unfold").append(Doc::line()).append(mk_let(
            t.clone(),
            &[],
            Doc::text("Type"),
            self.emit_type(env, body),
        ));
        let env = &mut env.clone();
        let this = env
            .push_this(TypeT::TypeRef(k.clone()).with_loc(name.loc.clone()))
            .with_loc(name.loc.clone());
        let this_arg = parens(
            Doc::text("[@@@mkey] ")
                .append(self.emit_name(Name::Var(this.val.clone())))
                .append(":")
                .append(Doc::line())
                .append(t),
        );

        let body = body.clone();
        let this_r = this.clone();
        let pred_decl = self.emit_pred_decl(
            SLPropVariant::Init {
                perm: &Doc::text("p"),
            },
            k,
            vec![this_arg.clone()],
            |s, variant, naming, props| {
                s.emit_type_slprop(env, &body, variant, naming, props, &mk_rvar(&this_r));
            },
        );

        let this_r = this.clone();
        let uninit_pred_decl = self.emit_pred_decl(
            SLPropVariant::Uninit,
            k,
            vec![this_arg],
            |s, variant, naming, props| {
                s.emit_type_slprop(env, &body, variant, naming, props, &mk_rvar(&this_r));
            },
        );

        // has_zero_default instance
        let default_name = self.emit_name(Name::TypeRefDefault(k.into()));
        let type_name = self.emit_name(Name::TypeRef(k.into()));
        let default_decl = mk_instance(
            default_name,
            &[],
            unaryfn(Doc::text("has_zero_default"), type_name),
            Doc::text("{")
                .append(Doc::line())
                .append(
                    Doc::text("zero_default =")
                        .append(Doc::line())
                        .append(self.emit_type_default(env, &body))
                        .group(),
                )
                .nest(2)
                .append(Doc::line())
                .append("}")
                .group(),
        );

        Doc::intersperse(
            vec![ty_decl, pred_decl, uninit_pred_decl, default_decl],
            Doc::line(),
        )
    }
} // impl Emitter (group D)

fn mk_attrs(attrs: Vec<Doc>) -> Doc {
    if attrs.is_empty() {
        return Doc::nil();
    }
    Doc::text("[@@")
        .append(Doc::intersperse(attrs, Doc::text(";").append(Doc::line())))
        .append("]")
        .group()
        .nest(2)
        .append(Doc::line())
}

/// Recognize an assertion condition that is syntactically the constant false.
///
/// `_assert` bodies are C-preprocessed, so a source-level `false` reaches us as
/// the integer literal `0` once `<stdbool.h>` has had its way, and it may be
/// wrapped in whatever casts the surrounding macro applied. Look through casts
/// and accept either spelling.
fn is_statically_false(e: &Rc<Expr>) -> bool {
    match &e.val {
        ExprT::BoolLit(b) => !b,
        ExprT::IntLit(n, _) => **n == BigInt::from(0),
        ExprT::Cast(inner, _) => is_statically_false(inner),
        _ => false,
    }
}

fn mk_assume_val(attrs: Vec<Doc>, n: Doc, args: &[Doc], ty: Doc) -> Doc {
    mk_attrs(attrs)
        .append(
            Doc::text("assume val")
                .append(Doc::line())
                .append(n)
                .group()
                .append(
                    Doc::concat(args.iter().map(|arg| Doc::line().append(arg.clone())))
                        .append(Doc::line().append(":"))
                        .group(),
                )
                .group()
                .append(Doc::line().append(ty).nest(2))
                .nest(2)
                .group(),
        )
        .group()
}

fn mk_sizeof_pos_axiom(name: Doc, ty: Doc) -> Doc {
    let ty_arg = parens(
        Doc::text("a: Type0 { a ==")
            .append(Doc::line())
            .append(ty)
            .append(Doc::line())
            .append("}")
            .group(),
    );
    let sizeof = unaryfn(Doc::text("Pulse.Lib.C.Sizeof.c_sizeof"), Doc::text("a"));
    let sizeof_value = unaryfn(Doc::text("FStar.SizeT.v"), sizeof);
    mk_assume_val(
        vec![],
        name,
        &[ty_arg],
        Doc::text("Lemma")
            .append(Doc::line())
            .append(parens(sizeof_value.clone().append(Doc::text(" > 0"))))
            .append(Doc::line())
            .append(
                Doc::text("[SMTPat ")
                    .append(sizeof_value)
                    .append(Doc::text("]")),
            ),
    )
}

fn mk_fun(arg: Doc, body: Doc) -> Doc {
    parens(
        Doc::text("fun")
            .append(Doc::line())
            .append(arg)
            .append(Doc::line())
            .append("->")
            .group()
            .nest(2)
            .append(Doc::line())
            .append(body),
    )
}

fn mk_thunk(body: Doc) -> Doc {
    mk_fun(Doc::text("_"), body)
}

impl<'a> Emitter<'a> {
    fn emit_struct_decl(&mut self, _env: &Env, name: &Ident) -> Doc {
        let k = &TypeRefKind::Struct(name.clone().into());
        let struct_type_name = self.emit_name(Name::TypeRef(k.into()));
        let pts_to_name = self.emit_name(Name::TypeRefPred(k.into()));
        let uninit_pred_name = self.emit_name(Name::TypeRefUninitPred(k.into()));
        let default_name = self.emit_name(Name::TypeRefDefault(k.into()));
        let default_value_name = self.emit_name(Name::StructAuxFn(
            name.val.clone(),
            "zero_default".to_string(),
        ));

        Doc::intersperse(
            [
                Doc::text("assume val")
                    .append(Doc::line())
                    .append(struct_type_name.clone())
                    .append(Doc::line())
                    .append(": Type0")
                    .group(),
                Doc::text("assume val")
                    .append(Doc::line())
                    .append(pts_to_name)
                    .append(Doc::line())
                    .append(":")
                    .append(Doc::line())
                    .append(struct_type_name.clone())
                    .append(Doc::line())
                    .append("->")
                    .append(Doc::line())
                    .append("perm")
                    .append(Doc::line())
                    .append("->")
                    .append(Doc::line())
                    .append("slprop")
                    .group(),
                Doc::text("assume val")
                    .append(Doc::line())
                    .append(uninit_pred_name)
                    .append(Doc::line())
                    .append(":")
                    .append(Doc::line())
                    .append(struct_type_name.clone())
                    .append(Doc::line())
                    .append("->")
                    .append(Doc::line())
                    .append("slprop")
                    .group(),
                Doc::text("assume val")
                    .append(Doc::line())
                    .append(default_value_name.clone())
                    .append(Doc::line())
                    .append(":")
                    .append(Doc::line())
                    .append(struct_type_name.clone())
                    .group(),
                mk_instance(
                    default_name,
                    &[],
                    unaryfn(Doc::text("has_zero_default"), struct_type_name.clone()),
                    Doc::text("{ zero_default = ")
                        .append(default_value_name)
                        .append(" }")
                        .group(),
                ),
            ],
            Doc::hardline(),
        )
    }

    fn emit_structdefn(
        &mut self,
        env: &Env,
        decl @ StructDefn { name, fields, .. }: &StructDefn,
    ) -> Doc {
        let env = &mut env.clone();
        env.push_struct(decl.clone());

        // Track which struct we're defining so self-referential pointer
        // fields don't produce infinitely recursive predicates.
        self.defining_struct = Some(name.val.clone());

        let k = &TypeRefKind::Struct(name.clone());
        let struct_type_name = self.emit_name(Name::TypeRef(k.into()));
        let ref_struct_type = unaryfn(Doc::text("ref"), struct_type_name.clone());

        let direct_fld =
            |fld: &Ident| Name::StructDirectFieldName(name.val.clone(), fld.val.clone());

        let mut ses = vec![];

        ses.push(
            Doc::text("noeq type")
                .append(Doc::line())
                .append(struct_type_name.clone())
                .append(Doc::line())
                .append("=")
                .append(Doc::line())
                .append("{")
                .group()
                .append(Doc::concat(fields.iter().map(|f| {
                    let fld = f.val.name();
                    Doc::hardline().append(
                        self.emit_name(direct_fld(fld))
                            .append(":")
                            .append(Doc::line())
                            .append(self.emit_field_record_type(env, f))
                            .append(";")
                            .group()
                            .nest(2),
                    )
                })))
                .nest(2)
                .append(Doc::line())
                .append("}")
                .group(),
        );
        if env.occupies_space(TypeT::TypeRef(k.clone()).with_loc(name.loc.clone()).into()) {
            ses.push(mk_sizeof_pos_axiom(
                self.emit_name(Name::TypeRefSizeofPos(k.into())),
                struct_type_name.clone(),
            ));
        }

        // Generate struct spec type and pred by gathering slprops from fields
        let env = &mut env.clone();
        let this = env
            .push_this(TypeT::TypeRef(k.clone()).with_loc(name.loc.clone()))
            .with_loc(name.loc.clone());
        let this_doc = Doc::text(self.nm.mangle(&Name::Var(this.val.clone())).to_string());
        let this_arg = parens(
            Doc::text("[@@@mkey] ")
                .append(this_doc.clone())
                .append(":")
                .append(Doc::line())
                .append(struct_type_name.clone()),
        );

        // Determine the spec param name (e.g., "val_simple_0")
        let spec_param_name =
            Doc::text(self.nm.mangle(&Name::Val(name.val.clone(), 0)).to_string());

        // Collect per-field spec info using emit_type_slprop with SpecRecord naming.
        // Inline array fields (`T arr[N];`) are NOT tracked in the struct's spec
        // record / pred — they are inline storage and their value is captured
        // directly in the struct's record value.
        let type_ref = TypeRef::from(k);
        let field_specs: Vec<FieldSpecInfo> = fields
            .iter()
            .filter(|f| !f.val.is_array())
            .map(|f| {
                let fld = f.val.name();
                let fld_ty = f.val.logical_type(&f.loc);
                let field_name: Rc<IdentT> = fld.val.clone();
                let mut bindings = vec![];
                let mut init_props = vec![];
                let field_expr =
                    ExprT::Member(mk_rvar(&this), fld.clone().into()).with_loc(fld.loc.clone());
                let mut naming = ValNaming::SpecRecord {
                    spec_param: &spec_param_name,
                    type_ref: &type_ref,
                    field_name: &field_name,
                    bindings: &mut bindings,
                };
                self.emit_type_slprop(
                    env,
                    &fld_ty,
                    SLPropVariant::Init {
                        perm: &Doc::text("p"),
                    },
                    &mut naming,
                    &mut init_props,
                    &field_expr,
                );
                drop(naming);
                FieldSpecInfo {
                    field_ident: field_name,
                    bindings,
                    init_props,
                }
            })
            .collect();

        // Flatten all spec bindings across fields
        let all_spec_bindings: Vec<&SpecFieldBinding> = field_specs
            .iter()
            .flat_map(|fs| fs.bindings.iter())
            .collect();

        // Emit the spec record type if there are any spec bindings
        // Use mangle for definition (local), force qualification for storage (cross-module use)
        let spec_type_name_local =
            Doc::text(self.nm.mangle(&Name::TypeRefSpec(k.into())).to_string());
        let spec_mangled = self.nm.mangle(&Name::TypeRefSpec(k.into())).to_string();
        let spec_type_name_qualified =
            if let Some(owner) = module_for_name(&Name::TypeRefSpec(k.into())) {
                Doc::text(format!("{}.{}", owner, spec_mangled))
            } else {
                Doc::text(spec_mangled)
            };
        if !all_spec_bindings.is_empty() {
            ses.push(
                Doc::text("[@@erasable] noeq type")
                    .append(Doc::line())
                    .append(spec_type_name_local.clone())
                    .append(Doc::line())
                    .append("=")
                    .append(Doc::line())
                    .append("{")
                    .group()
                    .append(Doc::concat(all_spec_bindings.iter().map(|b| {
                        Doc::hardline().append(
                            b.field_name
                                .clone()
                                .append(":")
                                .append(Doc::line())
                                .append(b.ty.clone())
                                .append(";")
                                .group()
                                .nest(2),
                        )
                    })))
                    .nest(2)
                    .append(Doc::line())
                    .append("}")
                    .group(),
            );
        }

        // Register the spec type as the single val param for this struct's TypeRef
        if all_spec_bindings.is_empty() {
            self.type_val_params.insert(TypeRef::from(k), vec![]);
        } else {
            self.type_val_params
                .insert(TypeRef::from(k), vec![spec_type_name_qualified.clone()]);
        }

        // Collect init props from field specs
        let mut init_props: Vec<Doc> = field_specs
            .iter()
            .flat_map(|fs| fs.init_props.clone())
            .collect();

        // A flexible array member with a `_refines(...)` length refinement
        // contributes a `pure` length relation to the struct predicate (e.g.
        // `array_spec_len this.data == UInt32.v this.len`). The refinement is
        // elaborated with the array bound to `this`; rewrite it so the array
        // becomes the struct field `this.<fam>` and sibling references become
        // `this.<sibling>`.
        for f in fields {
            if let Some((_, Some(pred))) = f.val.flex_array_info() {
                let fam_field: Rc<Ident> = Rc::new(f.val.name().clone());
                let subst = subst_flex_refine_pred(pred, &fam_field, &this);
                // The refinement is `_slprop`-typed, so `emit_rvalue` already
                // renders it as an slprop (`with_pure (..)`).
                init_props.push(self.emit_rvalue(env, &subst));
            }
        }

        // Emit __pred directly (no indirection via __pred')
        let pred_name = Doc::text(self.nm.mangle(&Name::TypeRefPred(k.into())).to_string());
        if !all_spec_bindings.is_empty() {
            let pred_args = vec![
                this_arg.clone(),
                parens(Doc::text("p: perm")),
                parens(
                    spec_param_name
                        .clone()
                        .append(":")
                        .append(Doc::line())
                        .append(spec_type_name_local.clone()),
                ),
            ];
            if decl.eager_unfold_pred {
                ses.push(mk_eager_unfold_slprop(
                    pred_name.clone(),
                    &pred_args,
                    mk_star(init_props.iter().cloned()),
                ));
            } else {
                ses.push(
                    Doc::text("let")
                        .append(Doc::line())
                        .append("predicate")
                        .append(Doc::line())
                        .append(pred_name.clone())
                        .group()
                        .append(
                            Doc::concat(
                                pred_args.iter().map(|arg| Doc::line().append(arg.clone())),
                            )
                            .nest(2)
                            .append(Doc::line().append("=").group()),
                        )
                        .group()
                        .nest(2)
                        .group()
                        .append(Doc::line().append(mk_star(init_props.iter().cloned())))
                        .group()
                        .nest(2),
                );
            }
        } else {
            // No spec bindings. Emit a simple pred with just this and perm; its
            // body is `emp` unless a flexible-array-member length refinement
            // contributes a `pure` fact.
            let body = if init_props.is_empty() {
                Doc::text("emp")
            } else {
                mk_star(init_props.iter().cloned())
            };
            ses.push(mk_eager_unfold_slprop(
                pred_name.clone(),
                &[this_arg.clone(), parens(Doc::text("p: perm"))],
                body,
            ));
        }

        // Emit uninit pred (stays as [@@pulse_eager_unfold])
        // Use the old emit_pred_decl approach since uninit may need val params (e.g., arrays)
        {
            let this_r = this.clone();
            let emit_uninit_slprops = |s: &mut Self,
                                       variant: SLPropVariant,
                                       naming: &mut ValNaming,
                                       props: &mut Vec<Doc>| {
                for f in fields {
                    if f.val.is_array() {
                        // Inline array fields are not tracked in the uninit pred.
                        continue;
                    }
                    let fld = f.val.name();
                    let fld_ty = f.val.logical_type(&f.loc);
                    let field_expr = ExprT::Member(mk_rvar(&this_r), fld.clone().into())
                        .with_loc(fld.loc.clone());
                    s.emit_type_slprop(env, &fld_ty, variant, naming, props, &field_expr);
                }
            };
            ses.push(self.emit_pred_decl(
                SLPropVariant::Uninit,
                k,
                vec![this_arg.clone()],
                &emit_uninit_slprops,
            ));
        }

        // Emit __pred_unfold ghost fn
        if !decl.eager_unfold_pred && !all_spec_bindings.is_empty() {
            let unfold_name = Doc::text(
                self.nm
                    .mangle(&Name::TypeRefPredUnfold(k.into()))
                    .to_string(),
            );
            let requires_doc = nary_no_parens([
                pred_name.clone(),
                this_doc.clone(),
                Doc::text("p"),
                spec_param_name.clone(),
            ]);

            ses.push(
                Doc::text("[@@pulse_intro]")
                    .append(Doc::hardline())
                    .append(
                        Doc::text("ghost fn")
                            .append(Doc::line())
                            .append(unfold_name),
                    )
                    .group()
                    .append(
                        Doc::hardline()
                            .append("    (")
                            .append(this_doc.clone())
                            .append(": ")
                            .append(struct_type_name.clone())
                            .append(")"),
                    )
                    .append(Doc::hardline().append("    (p: perm)"))
                    .append(
                        Doc::hardline()
                            .append("    (")
                            .append(spec_param_name.clone())
                            .append(": ")
                            .append(spec_type_name_local.clone())
                            .append(")"),
                    )
                    .append(Doc::hardline().append("  requires ").append(requires_doc))
                    .append(Doc::concat(init_props.iter().map(|e| {
                        Doc::hardline().append("  ensures ").append(e.clone())
                    })))
                    .append(Doc::hardline().append("{"))
                    .append(Doc::hardline().append("  unfold ").append(nary_no_parens([
                        pred_name.clone(),
                        this_doc.clone(),
                        Doc::text("p"),
                        spec_param_name.clone(),
                    ])))
                    .append(Doc::hardline().append("}")),
            );
        }

        // Emit __pred_fold ghost fn
        if !decl.eager_unfold_pred && !all_spec_bindings.is_empty() {
            let fold_name = Doc::text(self.nm.mangle(&Name::TypeRefPredFold(k.into())).to_string());

            // Build per-binding val params for fold
            let mut fold_val_params: Vec<Doc> = vec![];
            let mut fold_spec_record_fields: Vec<Doc> = vec![];
            for fs in &field_specs {
                for (i, binding) in fs.bindings.iter().enumerate() {
                    let val_name = Doc::text(
                        self.nm
                            .mangle(&Name::Val(fs.field_ident.clone(), i as u32))
                            .to_string(),
                    );
                    fold_val_params.push(
                        Doc::text("    (")
                            .append(val_name.clone())
                            .append(": ")
                            .append(binding.ty.clone())
                            .append(")"),
                    );
                    fold_spec_record_fields.push(
                        Doc::hardline()
                            .append("    ")
                            .append(binding.field_name.clone())
                            .append(" = ")
                            .append(val_name)
                            .append(";"),
                    );
                }
            }

            // Generate init props using individual val names (per-field Standard naming)
            let mut fold_requires = vec![];
            for f in fields {
                if f.val.is_array() {
                    // Inline array fields are not tracked in the pred / spec record.
                    continue;
                }
                let fld = f.val.name();
                let fld_ty = f.val.logical_type(&f.loc);
                let field_expr =
                    ExprT::Member(mk_rvar(&this), fld.clone().into()).with_loc(fld.loc.clone());
                let mut field_bindings = vec![];
                let mut naming = ValNaming::Standard {
                    quote: false,
                    bindings: &mut field_bindings,
                };
                self.emit_type_slprop(
                    env,
                    &fld_ty,
                    SLPropVariant::Init {
                        perm: &Doc::text("p"),
                    },
                    &mut naming,
                    &mut fold_requires,
                    &field_expr,
                );
            }

            // Build the spec record literal for ensures
            let spec_record_literal = parens(
                Doc::text("{")
                    .append(Doc::concat(fold_spec_record_fields))
                    .append(Doc::hardline())
                    .append("  }"),
            );

            let ensures_doc = nary_no_parens([
                pred_name.clone(),
                this_doc.clone(),
                Doc::text("p"),
                spec_record_literal.clone(),
            ]);

            ses.push(
                Doc::text("[@@pulse_intro]")
                    .append(Doc::hardline())
                    .append(Doc::text("ghost fn").append(Doc::line()).append(fold_name))
                    .group()
                    .append(
                        Doc::hardline()
                            .append("    (")
                            .append(this_doc.clone())
                            .append(": ")
                            .append(struct_type_name.clone())
                            .append(")"),
                    )
                    .append(Doc::hardline().append("    (p: perm)"))
                    .append(Doc::concat(
                        fold_val_params
                            .iter()
                            .map(|p| Doc::hardline().append(p.clone())),
                    ))
                    .append(Doc::concat(fold_requires.iter().map(|r| {
                        Doc::hardline().append("  requires ").append(r.clone())
                    })))
                    .append(Doc::hardline().append("  ensures ").append(ensures_doc))
                    .append(Doc::hardline().append("{"))
                    .append(Doc::hardline().append("  fold ").append(nary_no_parens([
                        pred_name.clone(),
                        this_doc.clone(),
                        Doc::text("p"),
                        spec_record_literal,
                    ])))
                    .append(Doc::hardline().append("}")),
            );
        }

        let unfolded_tok =
            self.emit_name(Name::StructAuxFn(name.val.clone(), "raw_unfolded".into()));
        ses.push(mk_assume_val(
            vec![],
            unfolded_tok.clone(),
            &[
                parens(
                    Doc::text("[@@@mkey] x:")
                        .append(Doc::line())
                        .append(ref_struct_type.clone()),
                ),
                parens(Doc::text("p: perm")),
            ],
            Doc::text("slprop"),
        ));

        let ghost_fld = |fld: &Ident| Name::StructGhostFieldProj(name.val.clone(), fld.val.clone());

        for f in fields {
            let fld = f.val.name();
            // Ghost projection:
            //   - `Plain` fields: `ref T` (ties to a value cell via `pts_to`).
            //   - Inline-array fields: the array *handle* itself
            //     (no `ref` wrapper); `aux_raw_unfold` ties it to the
            //     noeq's `<fld>` (contents) via `array_pts_to`.
            let projected_type = self.emit_field_projection_type(env, f);

            ses.push(mk_assume_val(
                vec![],
                self.emit_name(ghost_fld(fld)),
                &[parens(
                    Doc::text("x:")
                        .append(Doc::line())
                        .append(ref_struct_type.clone()),
                )],
                Doc::text("GTot")
                    .append(Doc::line())
                    .append(projected_type)
                    .group(),
            ));
        }

        // For every field, emit the inverse of the field-address projection: a
        // total function mapping the field's `ref` (or, for inline-array fields,
        // the array handle) back to a `ref` of the enclosing struct, plus a
        // left-inverse lemma (`container (proj p) == p`). The `SMTPat` triggers
        // on the round-trip term `container (proj p)` rather than the bare
        // projection, so the equality is injected only where a `container_of`
        // was actually formed — not in every proof that mentions a field
        // projection. The user composes `container_of` out of these symbols.
        for f in fields {
            let fld = f.val.name();
            let projected_type = self.emit_field_projection_type(env, f);
            let container_name =
                self.emit_name(Name::StructContainerFn(name.val.clone(), fld.val.clone()));

            ses.push(mk_assume_val(
                vec![],
                container_name.clone(),
                &[parens(
                    Doc::text("r:").append(Doc::line()).append(projected_type),
                )],
                ref_struct_type.clone(),
            ));

            let proj_name = self.emit_name(ghost_fld(fld));
            let inv_name =
                self.emit_name(Name::StructContainerInv(name.val.clone(), fld.val.clone()));
            let proj_app = unaryfn(proj_name, Doc::text("p"));
            let container_app = unaryfn(container_name, proj_app);
            let ensures = parens(
                Doc::text("ensures")
                    .append(Doc::line())
                    .append(container_app.clone())
                    .append(Doc::text(" == p")),
            );
            let smtpat = Doc::text("[SMTPat ")
                .append(container_app)
                .append(Doc::text("]"));

            ses.push(mk_assume_val(
                vec![],
                inv_name,
                &[parens(
                    Doc::text("p:")
                        .append(Doc::line())
                        .append(ref_struct_type.clone()),
                )],
                Doc::text("Lemma")
                    .append(Doc::line().append(ensures))
                    .append(Doc::line().append(smtpat))
                    .nest(2)
                    .group(),
            ));

            // Dual (right-inverse) lemma: `proj (container r) == r`. Sound for
            // the same reason as `container_inv` -- both compose the field
            // offset with its negation. Needed so a caller owning the struct via
            // `container_of(field_ref)` can still address the field through the
            // original `field_ref`: the SMTPat rewrites the round-trip term
            // `proj (container r)` back to `r`.
            let projected_type_dual = self.emit_field_projection_type(env, f);
            let container_name_dual =
                self.emit_name(Name::StructContainerFn(name.val.clone(), fld.val.clone()));
            let proj_name_dual = self.emit_name(ghost_fld(fld));
            let dual_name = self.emit_name(Name::StructProjContainerInv(
                name.val.clone(),
                fld.val.clone(),
            ));
            let container_app_r = unaryfn(container_name_dual, Doc::text("r"));
            let proj_container_app = unaryfn(proj_name_dual, container_app_r);
            let ensures_dual = parens(
                Doc::text("ensures")
                    .append(Doc::line())
                    .append(proj_container_app.clone())
                    .append(Doc::text(" == r")),
            );
            let smtpat_dual = Doc::text("[SMTPat ")
                .append(proj_container_app)
                .append(Doc::text("]"));

            ses.push(mk_assume_val(
                vec![],
                dual_name,
                &[parens(
                    Doc::text("r:")
                        .append(Doc::line())
                        .append(projected_type_dual),
                )],
                Doc::text("Lemma")
                    .append(Doc::line().append(ensures_dual))
                    .append(Doc::line().append(smtpat_dual))
                    .nest(2)
                    .group(),
            ));
        }

        // Offset-0 `container_of` null-preservation axiom.
        //
        // `container_of` on a struct's *first* (offset-0) member is pointer
        // identity (C 6.7.2.1: no leading padding). We capture this for the
        // null pointer with a single ground `squash` axiom on the field
        // projection (which fires automatically into the SMT context):
        //
        //   proj (null #outer) == null #inner
        //
        // The dual direction, `container (null #inner) == null #outer`, is NOT
        // emitted separately: it follows automatically from the `container_inv`
        // lemma (`container (proj p) == p`, carrying an SMTPat) instantiated at
        // `p = null`, rewritten with the axiom above. Sound ONLY at offset 0 —
        // a nonzero-offset `container_of(NULL)` is undefined behaviour — so we
        // restrict to the first field, and only when it is a `Plain`
        // (non-array, non-bitfield) member whose projection is a genuine `ref`.
        if let Some(f0) = fields.first() {
            if !f0.val.is_array() {
                if let FieldT::Plain { ty, .. } = &f0.val {
                    let fld = f0.val.name();
                    let inner_ty = self.emit_type(env, ty);
                    let null_inner =
                        parens(Doc::text("Pulse.Lib.Reference.null #").append(parens(inner_ty)));
                    let null_outer = parens(
                        Doc::text("Pulse.Lib.Reference.null #")
                            .append(parens(struct_type_name.clone())),
                    );

                    let proj_name = self.emit_name(ghost_fld(fld));
                    let proj_eq = parens(
                        unaryfn(proj_name, null_outer)
                            .append(Doc::text(" =="))
                            .append(Doc::line())
                            .append(null_inner),
                    );
                    ses.push(mk_assume_val(
                        vec![],
                        self.emit_name(Name::StructProjNull(name.val.clone(), fld.val.clone())),
                        &[],
                        unaryfn(Doc::text("squash"), proj_eq),
                    ));
                }
            }
        }

        ses.push(mk_assume_val(
            vec![Doc::text("pulse_intro")],
            self.emit_name(Name::StructAuxFn(name.val.clone(), "raw_unfold".into())),
            &[
                parens(
                    Doc::text("x:")
                        .append(Doc::line())
                        .append(ref_struct_type.clone()),
                ),
                parens(Doc::text("#p: perm")),
                parens(
                    Doc::text("vx:")
                        .append(Doc::line())
                        .append(struct_type_name.clone()),
                ),
            ],
            naryfn([
                Doc::text("stt_ghost"),
                Doc::text("unit"),
                Doc::text("emp_inames"),
                // pre
                naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to"),
                    Doc::text("x"),
                    Doc::text("#p"),
                    Doc::text("vx"),
                ]),
                {
                    let mut post = vec![naryfn([
                        unfolded_tok.clone(),
                        Doc::text("x"),
                        Doc::text("p"),
                    ])];
                    for f in fields {
                        let fld = f.val.name();
                        if f.val.is_array() {
                            // Inline array: tie the ghost array handle
                            // `__<fld>_1 x` to the contents stored in
                            // the noeq value at `vx.<fld>`. The noeq
                            // refines `vx.<fld>` to `full_array_spec`
                            // (refinement subtype of `array_spec`), so
                            // `array_pts_to` accepts it directly and the
                            // caller can still recover `array_pts_to_full`
                            // when needed.
                            post.push(naryfn([
                                Doc::text("array_pts_to"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                                Doc::text("p"),
                                Doc::text("vx.").append(self.emit_name(direct_fld(fld))),
                            ]));
                        } else {
                            post.push(naryfn([
                                Doc::text("Pulse.Lib.Reference.pts_to"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                                Doc::text("#p"),
                                Doc::text("vx.").append(self.emit_name(direct_fld(fld))),
                            ]));
                        }
                    }
                    mk_thunk(mk_star(post))
                },
            ]),
        ));

        let fold_arg_name = |fld: &Ident| Doc::text(format!("v_{}", fld));
        ses.push(mk_assume_val(
            vec![Doc::text("pulse_intro")],
            self.emit_name(Name::StructAuxFn(name.val.clone(), "raw_fold".into())),
            &{
                let mut args = vec![
                    parens(
                        Doc::text("x:")
                            .append(Doc::line())
                            .append(ref_struct_type.clone()),
                    ),
                    parens(Doc::text("#p: perm")),
                ];
                // Every field (Plain or Array) contributes a value arg
                // so we can construct the resulting struct record
                // literal. Inline-array args are annotated with the
                // refined `full_array_spec` type so the length refinement
                // is discharged at fold time rather than inferred.
                for f in fields {
                    let fld = f.val.name();
                    if f.val.is_array() {
                        args.push(parens(
                            fold_arg_name(fld)
                                .append(":")
                                .append(Doc::line())
                                .append(self.emit_field_record_type(env, f)),
                        ));
                    } else {
                        args.push(fold_arg_name(fld));
                    }
                }
                args
            },
            naryfn([
                Doc::text("stt_ghost"),
                Doc::text("unit"),
                Doc::text("emp_inames"),
                {
                    let mut pre = vec![naryfn([
                        unfolded_tok.clone(),
                        Doc::text("x"),
                        Doc::text("p"),
                    ])];
                    for f in fields {
                        let fld = f.val.name();
                        if f.val.is_array() {
                            // Inline array: consume `array_pts_to` on the
                            // ghost handle so the resulting struct value
                            // carries the contents in `vx.<fld>`. The
                            // refined `full_array_spec` type of `v_<fld>`
                            // is a subtype of `array_spec`, so the call
                            // typechecks and full-ness is preserved.
                            pre.push(naryfn([
                                Doc::text("array_pts_to"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                                Doc::text("p"),
                                fold_arg_name(fld),
                            ]));
                        } else {
                            pre.push(naryfn([
                                Doc::text("Pulse.Lib.Reference.pts_to"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                                Doc::text("#p"),
                                fold_arg_name(fld),
                            ]));
                        }
                    }
                    mk_star(pre)
                },
                mk_thunk(naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to"),
                    Doc::text("x"),
                    Doc::text("#p"),
                    Doc::text("{")
                        .append(Doc::concat(fields.iter().map(|f| {
                            let fld = f.val.name();
                            Doc::line()
                                .append(self.emit_name(direct_fld(fld)))
                                .append("=")
                                .append(fold_arg_name(fld))
                                .append(";")
                        })))
                        .nest(2)
                        .append(Doc::line())
                        .append("}")
                        .group(),
                ])),
            ]),
        ));
        ses.push(mk_assume_val(
            vec![Doc::text("pulse_intro")],
            self.emit_name(Name::StructAuxFn(
                name.val.clone(),
                "raw_fold_uninit".into(),
            )),
            &[parens(
                Doc::text("x:")
                    .append(Doc::line())
                    .append(ref_struct_type.clone()),
            )],
            naryfn([
                Doc::text("stt_ghost"),
                Doc::text("unit"),
                Doc::text("emp_inames"),
                {
                    let mut pre = vec![naryfn([
                        unfolded_tok.clone(),
                        Doc::text("x"),
                        Doc::text("1.0R"),
                    ])];
                    for f in fields {
                        let fld = f.val.name();
                        if f.val.is_array() {
                            // Inline array: the storage exists but is
                            // uninitialised; track it via
                            // `array_pts_to_uninit'` (no spec needed).
                            pre.push(naryfn([
                                Doc::text("array_pts_to_uninit'"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            ]));
                        } else {
                            pre.push(naryfn([
                                Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            ]));
                        }
                    }
                    mk_star(pre)
                },
                mk_thunk(naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                    Doc::text("x"),
                ])),
            ]),
        ));
        ses.push(mk_assume_val(
            vec![],
            self.emit_name(Name::StructAuxFn(
                name.val.clone(),
                "raw_unfold_uninit".into(),
            )),
            &[parens(
                Doc::text("x:")
                    .append(Doc::line())
                    .append(ref_struct_type.clone()),
            )],
            naryfn([
                Doc::text("stt_ghost"),
                Doc::text("unit"),
                Doc::text("emp_inames"),
                naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                    Doc::text("x"),
                ]),
                mk_thunk({
                    let mut post = vec![naryfn([
                        unfolded_tok.clone(),
                        Doc::text("x"),
                        Doc::text("1.0R"),
                    ])];
                    for f in fields {
                        let fld = f.val.name();
                        if f.val.is_array() {
                            post.push(naryfn([
                                Doc::text("array_pts_to_uninit'"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            ]));
                        } else {
                            post.push(naryfn([
                                Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            ]));
                        }
                    }
                    mk_star(post)
                }),
            ]),
        ));

        // Sized flexible-array-member allocators. When the struct has a
        // flexible array member, `malloc(sizeof(S) + n*sizeof(E))` and
        // `calloc(1, sizeof(S) + n*sizeof(E))` thread the tail length `n`.
        // Each axiom returns the struct in UNFOLDED form: the `aux_raw_unfolded`
        // token, every non-flex field uninitialized, and the flexible tail as a
        // length-`n` `array_pts_to` (uninitialized for malloc, zeroed for
        // calloc), plus `freeable`. The caller sets the length field and, for
        // malloc, fills the tail; the `[@@pulse_intro]` `aux_raw_fold` then
        // auto-folds back into a valid struct at escape.
        if fields.iter().any(|f| f.val.flex_array_info().is_some()) {
            for (flex_kind, zeroed) in [("malloc_flex", false), ("calloc_flex", true)] {
                let mut post = vec![naryfn([
                    unfolded_tok.clone(),
                    Doc::text("r"),
                    Doc::text("1.0R"),
                ])];
                for f in fields {
                    let fld = f.val.name();
                    if let Some((elem_ty, _)) = f.val.flex_array_info() {
                        let elem_doc = self.emit_type(env, elem_ty);
                        let spec = if zeroed {
                            naryfn([
                                Doc::text("array_spec_zeroed"),
                                elem_doc,
                                parens(Doc::text("FStar.SizeT.v n")),
                                Doc::text("zero_default"),
                            ])
                        } else {
                            naryfn([
                                Doc::text("array_spec_uninit"),
                                elem_doc,
                                parens(Doc::text("FStar.SizeT.v n")),
                            ])
                        };
                        post.push(naryfn([
                            Doc::text("array_pts_to"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("r")),
                            Doc::text("1.0R"),
                            spec,
                        ]));
                    } else if f.val.is_array() {
                        post.push(naryfn([
                            Doc::text("array_pts_to_uninit'"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("r")),
                        ]));
                    } else {
                        post.push(naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("r")),
                        ]));
                    }
                }
                post.push(naryfn([
                    Doc::text("Pulse.Lib.C.Ref.freeable"),
                    Doc::text("r"),
                ]));
                ses.push(mk_assume_val(
                    vec![],
                    self.emit_name(Name::StructAuxFn(name.val.clone(), flex_kind.into())),
                    &[parens(Doc::text("n: FStar.SizeT.t"))],
                    naryfn([
                        Doc::text("stt"),
                        ref_struct_type.clone(),
                        Doc::text("emp"),
                        mk_fun(Doc::text("r"), mk_star(post)),
                    ]),
                ));
            }
        }

        for f in fields {
            let fld = f.val.name();
            // Getter return type: for inline-array fields the array
            // *handle* itself (no `ref` wrapper) — same as the ghost
            // projection. For plain fields, `ref T`.
            let ret_type = self.emit_field_projection_type(env, f);
            let unfolded = naryfn([unfolded_tok.clone(), Doc::text("x"), Doc::text("p")]);
            ses.push(mk_assume_val(
                vec![Doc::text("pulse_impure_spec_no_proof_required")],
                self.emit_name(Name::StructFieldProj(name.val.clone(), fld.val.clone())),
                &[
                    parens(
                        Doc::text("x:")
                            .append(Doc::line())
                            .append(ref_struct_type.clone()),
                    ),
                    parens(Doc::text("#p: perm")),
                ],
                naryfn([
                    Doc::text("stt_atomic"),
                    ret_type,
                    Doc::text("#PulseCore.Observability.Neutral"),
                    Doc::text("emp_inames"),
                    unfolded.clone(),
                    mk_fun(
                        Doc::text("vx'"),
                        mk_star([
                            unfolded,
                            naryfn([
                                Doc::text("rewrites_to"),
                                Doc::text("vx'"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            ]),
                        ]),
                    ),
                ]),
            ))
        }

        // has_zero_default instance. For inline-array fields the
        // default is `array_spec_zeroed T (SizeT.v Nsz) zero_default`,
        // which is a `full_array_spec T` of length N satisfying the
        // noeq's `array_spec_len v == N` refinement.
        let default_name = self.emit_name(Name::TypeRefDefault(k.into()));
        ses.push(mk_instance(
            default_name,
            &[],
            unaryfn(Doc::text("has_zero_default"), struct_type_name.clone()),
            Doc::text("{")
                .append(Doc::line())
                .append(Doc::text("zero_default = {"))
                .append(Doc::concat(fields.iter().map(|f| {
                    let fld = f.val.name();
                    Doc::line()
                        .append(self.emit_name(direct_fld(fld)))
                        .append(" =")
                        .append(Doc::line())
                        .append(self.emit_field_default(env, f))
                        .append(";")
                        .group()
                        .nest(2)
                })))
                .nest(2)
                .append(Doc::line())
                .append("}")
                .append(Doc::line())
                .append("}")
                .group(),
        ));

        self.defining_struct = None;
        Doc::intersperse(ses.into_iter().map(|se| se.group()), Doc::hardline())
    }

    fn emit_uniondefn(&mut self, env: &Env, decl @ UnionDefn { name, fields }: &UnionDefn) -> Doc {
        let env = &mut env.clone();
        env.push_union(decl.clone());

        let k = &TypeRefKind::Union(name.clone());
        let union_type_name = self.emit_name(Name::TypeRef(k.into()));
        let pts_to_name = self.emit_name(Name::TypeRefPred(k.into()));
        let ref_union_type = unaryfn(Doc::text("ref"), union_type_name.clone());

        let field_ctor =
            |fld: &Ident| Name::UnionFieldConstructor(name.val.clone(), fld.val.clone());
        let ghost_fld = |fld: &Ident| Name::UnionGhostFieldProj(name.val.clone(), fld.val.clone());

        let mut ses = vec![];

        // Emit inductive type: noeq type union_foo = | Field_foo__x : Int32.t -> union_foo | ...
        ses.push(
            Doc::text("noeq type")
                .append(Doc::line())
                .append(union_type_name.clone())
                .append(Doc::line())
                .append("=")
                .append(Doc::concat(fields.iter().map(|f| {
                    let fld = f.val.name();
                    Doc::hardline().append(
                        Doc::text("| ")
                            .append(self.emit_name(field_ctor(fld)))
                            .append(Doc::text(" :"))
                            .append(Doc::line())
                            .append(self.emit_field_record_type(env, f))
                            .append(Doc::text(" ->"))
                            .append(Doc::line())
                            .append(union_type_name.clone())
                            .group()
                            .nest(2),
                    )
                })))
                .group(),
        );
        if env.occupies_space(TypeT::TypeRef(k.clone()).with_loc(name.loc.clone()).into()) {
            ses.push(mk_sizeof_pos_axiom(
                self.emit_name(Name::TypeRefSizeofPos(k.into())),
                union_type_name.clone(),
            ));
        }

        // Emit predicate (emp for MVP)
        let env = &mut env.clone();
        let this = env
            .push_this(TypeT::TypeRef(k.clone()).with_loc(name.loc.clone()))
            .with_loc(name.loc.clone());
        let all_args = vec![
            parens(
                Doc::text("[@@@mkey] ")
                    .append(self.emit_name(Name::Var(this.val.clone())))
                    .append(":")
                    .append(Doc::line())
                    .append(union_type_name.clone()),
            ),
            parens(Doc::text("p: perm")),
        ];
        self.type_val_params.insert(TypeRef::from(k), vec![]);
        self.type_uninit_val_params.insert(TypeRef::from(k), vec![]);
        ses.push(mk_eager_unfold_slprop(
            pts_to_name.clone(),
            &all_args,
            Doc::text("emp"),
        ));

        // Emit uninit predicate
        {
            let uninit_pred_name = self.emit_name(Name::TypeRefUninitPred(k.into()));
            let uninit_args = vec![parens(
                Doc::text("[@@@mkey] ")
                    .append(self.emit_name(Name::Var(this.val.clone())))
                    .append(":")
                    .append(Doc::line())
                    .append(union_type_name.clone()),
            )];
            ses.push(mk_eager_unfold_slprop(
                uninit_pred_name,
                &uninit_args,
                Doc::text("emp"),
            ));
        }

        // Emit unfolded token
        let unfolded_tok =
            |fld: &Ident| Name::UnionAuxFn(name.val.clone(), "raw_unfolded", fld.val.clone());
        for f in fields {
            let fld = f.val.name();
            ses.push(mk_assume_val(
                vec![],
                self.emit_name(unfolded_tok(fld)),
                &[
                    parens(
                        Doc::text("[@@@mkey] x:")
                            .append(Doc::line())
                            .append(ref_union_type.clone()),
                    ),
                    parens(Doc::text("p: perm")),
                ],
                Doc::text("slprop"),
            ));
        }

        // Emit ghost field projections.
        //   - Plain fields:        `ref T`
        //   - Inline-array fields: the refined array *handle* itself
        //     (no `ref` wrapper). `aux_raw_unfold` ties the noeq
        //     value's contents to this handle via `array_pts_to`.
        for f in fields {
            let fld = f.val.name();
            let projected_type = self.emit_field_projection_type(env, f);
            ses.push(mk_assume_val(
                vec![],
                self.emit_name(ghost_fld(fld)),
                &[parens(
                    Doc::text("x:")
                        .append(Doc::line())
                        .append(ref_union_type.clone()),
                )],
                Doc::text("GTot")
                    .append(Doc::line())
                    .append(projected_type)
                    .group(),
            ));
        }

        // Per-field unfold: requires pts_to x #p vx ** pure (Field_foo__x? vx)
        // gives back unfolded token plus the field's `pts_to` clause
        // tying the ghost projection to the active constructor's
        // payload. Uniform for plain and inline-array fields.
        for f in fields {
            let fld = f.val.name();
            let ctor_name = self.emit_name(field_ctor(fld));
            // vx has refined type: (vx: union_foo{Ctor? vx})
            let vx_refined_ty = parens(
                Doc::text("vx:").append(Doc::line()).append(
                    union_type_name
                        .clone()
                        .append("{")
                        .append(ctor_name.clone())
                        .append("?")
                        .append(Doc::line())
                        .append("vx}")
                        .group(),
                ),
            );
            let mut post_items: Vec<Doc> = vec![naryfn([
                self.emit_name(unfolded_tok(fld)),
                Doc::text("x"),
                Doc::text("p"),
            ])];
            let ctor_payload = parens(
                ctor_name
                    .clone()
                    .append("?._0")
                    .append(Doc::line())
                    .append("vx")
                    .group(),
            );
            if f.val.is_array() {
                post_items.push(naryfn([
                    Doc::text("array_pts_to"),
                    unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                    Doc::text("p"),
                    ctor_payload,
                ]));
            } else {
                post_items.push(naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to"),
                    unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                    Doc::text("#p"),
                    ctor_payload,
                ]));
            }
            ses.push(mk_assume_val(
                vec![Doc::text("pulse_intro")],
                self.emit_name(Name::UnionAuxFn(
                    name.val.clone(),
                    "raw_unfold",
                    fld.val.clone(),
                )),
                &[
                    parens(
                        Doc::text("x:")
                            .append(Doc::line())
                            .append(ref_union_type.clone()),
                    ),
                    parens(Doc::text("#p: perm")),
                    vx_refined_ty,
                ],
                naryfn([
                    Doc::text("stt_ghost"),
                    Doc::text("unit"),
                    Doc::text("emp_inames"),
                    naryfn([
                        Doc::text("Pulse.Lib.Reference.pts_to"),
                        Doc::text("x"),
                        Doc::text("#p"),
                        Doc::text("vx"),
                    ]),
                    mk_thunk(mk_star(post_items)),
                ]),
            ));

            // Per-field fold: symmetric — for inline arrays we consume
            // the `array_pts_to` of the ghost handle (so the constructor
            // value can carry the contents); for plain fields we consume
            // the field's `pts_to`.
            let fld_ty_doc = self.emit_field_record_type(env, f);
            let mut pre_items: Vec<Doc> = vec![naryfn([
                self.emit_name(unfolded_tok(fld)),
                Doc::text("x"),
                Doc::text("p"),
            ])];
            if f.val.is_array() {
                pre_items.push(naryfn([
                    Doc::text("array_pts_to"),
                    unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                    Doc::text("p"),
                    Doc::text(format!("v_{}", fld)),
                ]));
            } else {
                pre_items.push(naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to"),
                    unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                    Doc::text("#p"),
                    Doc::text(format!("v_{}", fld)),
                ]));
            }
            ses.push(mk_assume_val(
                vec![Doc::text("pulse_intro")],
                self.emit_name(Name::UnionAuxFn(
                    name.val.clone(),
                    "raw_fold",
                    fld.val.clone(),
                )),
                &[
                    parens(
                        Doc::text("x:")
                            .append(Doc::line())
                            .append(ref_union_type.clone()),
                    ),
                    parens(Doc::text("#p: perm")),
                    parens(
                        Doc::text(format!("v_{}:", fld))
                            .append(Doc::line())
                            .append(fld_ty_doc),
                    ),
                ],
                naryfn([
                    Doc::text("stt_ghost"),
                    Doc::text("unit"),
                    Doc::text("emp_inames"),
                    mk_star(pre_items),
                    mk_thunk(naryfn([
                        Doc::text("Pulse.Lib.Reference.pts_to"),
                        Doc::text("x"),
                        Doc::text("#p"),
                        unaryfn(ctor_name.clone(), Doc::text(format!("v_{}", fld))),
                    ])),
                ]),
            ));
        }

        // Field getter functions (stt_atomic, like structs).
        // For inline-array fields the getter returns the array handle
        // (no `ref` wrapper); for plain fields it returns `ref T`.
        for f in fields {
            let fld = f.val.name();
            let ret_type = self.emit_field_projection_type(env, f);
            let unfolded = naryfn([
                self.emit_name(unfolded_tok(fld)),
                Doc::text("x"),
                Doc::text("p"),
            ]);
            ses.push(mk_assume_val(
                vec![Doc::text("pulse_impure_spec_no_proof_required")],
                self.emit_name(Name::UnionFieldProj(name.val.clone(), fld.val.clone())),
                &[
                    parens(
                        Doc::text("x:")
                            .append(Doc::line())
                            .append(ref_union_type.clone()),
                    ),
                    parens(Doc::text("#p: perm")),
                ],
                naryfn([
                    Doc::text("stt_atomic"),
                    ret_type,
                    Doc::text("#PulseCore.Observability.Neutral"),
                    Doc::text("emp_inames"),
                    unfolded.clone(),
                    mk_fun(
                        Doc::text("vx'"),
                        mk_star([
                            unfolded,
                            naryfn([
                                Doc::text("rewrites_to"),
                                Doc::text("vx'"),
                                unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            ]),
                        ]),
                    ),
                ]),
            ))
        }

        // Ghost-axiom activation lemma for each arm.
        //
        // A write through a union arm `u->arm... = v` needs arm `arm` active,
        // but at an arbitrary program point the active arm is unknown, so the
        // arm's getter (which requires `Field_? vx`) is unusable. C semantics
        // say the write *activates* the arm.
        //
        // Activation is user-driven via `_ghost_stmt($activate(union U::arm) $(u))`.
        // We emit it as a ghost axiom (`assume val ... : stt_ghost ...`): given an
        // *uninitialized* union cell at `x` (`pts_to_uninit x`), it yields the arm
        // active with an *uninitialized* payload (`pts_to_uninit`). It commits to
        // NO field values -- sub-fields (or the scalar payload) become readable
        // only once physically written.
        //
        // The precondition is `pts_to_uninit x` (not full `pts_to x val`): a
        // caller holding an initialized union satisfies it automatically because
        // `Pulse.Lib.Reference.forget_init` is `[@@pulse_intro]`
        // (`pts_to r n |- pts_to_uninit r`), so its stored value is downgraded to
        // uninitialized on the way in. This mirrors C, where writing through a
        // union member leaves the previously-stored value unspecified.
        //
        // A ghost axiom (rather than a proven stateful `fn`) is used so that
        // activation is a pure specification step, *erased* at extraction with no
        // runtime effect. This matches C: the real arm write realizes the tag at
        // runtime (C17 6.2.6.1p7).
        //
        // Not `[@@pulse_intro]`: activation must stay explicit, never auto-fired.
        //
        // Emitted for every `Plain` arm (struct- or scalar-typed); bit-field
        // arms are skipped (their cell has a width refinement and no matching
        // uninit `forget_init`/getter shape).
        for f in fields {
            if matches!(&f.val, FieldT::BitField { .. }) {
                continue;
            }
            let fld = f.val.name();
            let unfolded = naryfn([
                self.emit_name(unfolded_tok(fld)),
                Doc::text("x"),
                Doc::text("1.0R"),
            ]);
            let ghost_proj = unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x"));

            // The arm's storage handed back on activation.
            //
            // For a scalar/struct arm the ghost projection is a `ref T`, so the
            // uninitialised cell is `Pulse.Lib.Reference.pts_to_uninit`.
            //
            // For an inline-array arm the projection is an array *handle*
            // (`array T`). `array_pts_to_uninit'` is well-typed but unusable:
            // it existentially hides the array length, so a subsequent indexed
            // write (`a->arm[i] = ...`) cannot discharge `i < length`. Instead
            // we mirror the arm's `aux_raw_unfold` and hand back a full
            // `array_pts_to` over an existential `full_array_lspec T n` value of
            // the arm's *static* length, so the length is known and in-bounds
            // writes verify. The contents stay existentially quantified, so
            // activation still commits to no element values (matching C, where
            // the previously-stored bytes are unspecified).
            let arm_uninit = if f.val.is_array() {
                let v_name = Doc::text(format!("v_{}", fld));
                wrap_exists(
                    &[ExBinding {
                        name: v_name.clone(),
                        ty: self.emit_field_record_type(env, f),
                    }],
                    vec![naryfn([
                        Doc::text("array_pts_to"),
                        ghost_proj,
                        Doc::text("1.0R"),
                        v_name,
                    ])],
                )
            } else {
                naryfn([Doc::text("Pulse.Lib.Reference.pts_to_uninit"), ghost_proj])
            };

            ses.push(mk_assume_val(
                vec![],
                self.emit_name(Name::UnionActivateFn(name.val.clone(), fld.val.clone())),
                &[parens(
                    Doc::text("x:")
                        .append(Doc::line())
                        .append(ref_union_type.clone()),
                )],
                naryfn([
                    Doc::text("stt_ghost"),
                    Doc::text("unit"),
                    Doc::text("emp_inames"),
                    naryfn([
                        Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                        Doc::text("x"),
                    ]),
                    mk_thunk(mk_star([unfolded, arm_uninit])),
                ]),
            ));
        }

        // has_zero_default instance (uses first field's constructor).
        // For an inline-array first field, the constructor wraps an
        // `array_spec_zeroed`-built `full_array_spec` of the static
        // length.
        if let Some(first_f) = fields.first() {
            let first_fld = first_f.val.name();
            let default_name = self.emit_name(Name::TypeRefDefault(k.into()));
            let first_ctor = self.emit_name(Name::UnionFieldConstructor(
                name.val.clone(),
                first_fld.val.clone(),
            ));
            ses.push(mk_instance(
                default_name,
                &[],
                unaryfn(Doc::text("has_zero_default"), union_type_name.clone()),
                Doc::text("{")
                    .append(Doc::line())
                    .append(
                        Doc::text("zero_default =")
                            .append(Doc::line())
                            .append(unaryfn(first_ctor, self.emit_field_default(env, first_f)))
                            .group(),
                    )
                    .nest(2)
                    .append(Doc::line())
                    .append("}")
                    .group(),
            ));
        }

        Doc::intersperse(ses.into_iter().map(|se| se.group()), Doc::hardline())
    }

    fn emit_fn_sig(&mut self, env: &Env, decl: &FnDecl) -> Doc {
        self.emit_fn_sig_inner(env, decl, false)
    }

    // ---- Function-pointer emission helpers (deep model) ----

    /// The module-qualified name of the fnptr wrapper `func_<g>__fp`.
    fn fnptr_wrap_name(&mut self, g: &str) -> Doc {
        self.emit_name(Name::Fn(Rc::from(format!("{}__fp", g))))
    }

    /// `pre_of`/`post_of` (total: `pre_of_tot`/`post_of_tot`) applied to the
    /// wrapper, recovering its inlined pre/post from its type.
    fn fnptr_pre_of(&mut self, g: &str, is_total: bool) -> Doc {
        let proj = if is_total {
            "Pulse.Lib.C.FuncPtr.pre_of_tot "
        } else {
            "Pulse.Lib.C.FuncPtr.pre_of "
        };
        parens(Doc::text(proj).append(self.fnptr_wrap_name(g)))
    }
    fn fnptr_post_of(&mut self, g: &str, is_total: bool) -> Doc {
        let proj = if is_total {
            "Pulse.Lib.C.FuncPtr.post_of_tot "
        } else {
            "Pulse.Lib.C.FuncPtr.post_of "
        };
        parens(Doc::text(proj).append(self.fnptr_wrap_name(g)))
    }

    /// `(Pulse.Lib.C.FuncPtr.of_fn (pre_of func_<g>__fp) (post_of func_<g>__fp)
    /// func_<g>__fp)` for a `_total` target, or `of_fn_div ..` for a divergent
    /// one (matching the `__fp` wrapper's effect and the validity divergence
    /// bit). The pre/post are recovered from the wrapper's type via the
    /// `pre_of`/`post_of` projectors.
    fn emit_of_fn(&mut self, env: &Env, g: &Ident) -> Doc {
        let is_total = env.lookup_fn(g).map(|d| d.is_total).unwrap_or(false);
        let of_fn = if is_total {
            "Pulse.Lib.C.FuncPtr.of_fn"
        } else {
            "Pulse.Lib.C.FuncPtr.of_fn_div"
        };
        let pre = self.fnptr_pre_of(&g.val, is_total);
        let post = self.fnptr_post_of(&g.val, is_total);
        let wrap = self.fnptr_wrap_name(&g.val);
        parens(naryfn([Doc::text(of_fn), pre, post, wrap]))
    }

    /// The fnptr domain for the given argument types. This MUST agree with
    /// `emit_fnptr_spec_core`'s domain so that a fnptr *type* (`emit_type`
    /// FnPtr) and the synthesized triple's specs share the same `ARG`.
    fn fnptr_domain(&mut self, env: &Env, args: &[Rc<Type>]) -> Doc {
        let docs: Vec<Doc> = args.iter().map(|a| self.emit_type(env, a)).collect();
        fnptr_domain_doc(docs)
    }

    fn emit_fnptr_arg_tuple(&mut self, env: &Env, args: &[Rc<Expr>]) -> Doc {
        // One tuple component per C argument (its plain value). Pointer
        // arguments pass their pointer value; the callee's spec carries the
        // pointee ownership (`pts_to`) via the general type-slprop path. `_old`
        // across an indirect call is not supported, so no old-value component
        // is threaded here.
        let mut comps: Vec<Doc> = vec![];
        for a in args {
            comps.push(self.emit_rvalue(env, a));
        }
        match comps.len() {
            0 => Doc::text("()"),
            1 => comps.into_iter().next().unwrap(),
            _ => parens(Doc::intersperse(comps, Doc::text(", "))),
        }
    }

    /// Compute the shared pre/post spec pieces for a fnptr contract (used by both
    /// the address-taken triple and callback-parameter specs).
    ///
    /// The pre/post are built from the decl's `requires`/`ensures` via the same
    /// general lowering as `emit_fn_sig_inner`: each parameter's ownership
    /// (`pts_to`/`__pred`) conjunct plus the pure requires/ensures. Pointer
    /// parameters get their default `pts_to` permission this way. `_old(*p)`
    /// across an indirect call is NOT supported (the FuncPtr contract
    /// `pre: a->slprop`, `post: a->b->slprop` is non-relational).
    fn emit_fnptr_spec_core(&mut self, env: &Env, decl: &FnDecl) -> FnPtrSpecCore {
        let env = &mut env.clone();

        let mut arg_names: Vec<Rc<Ident>> = vec![];
        let mut arg_ty_docs: Vec<Doc> = vec![];
        for (i, arg) in decl.args.iter().enumerate() {
            let n: Rc<Ident> = arg.name.clone().unwrap_or_else(|| {
                Rc::<str>::from(format!("_unnamed{}", i)).with_loc(arg.ty.loc.clone())
            });
            arg_ty_docs.push(self.emit_type(env, &arg.ty));
            arg_names.push(n.clone());
            env.push_arg(arg, LocalDeclKind::RValue);
        }
        // Domain: one component per C argument, in argument order. Pointer
        // arguments contribute their pointer type; the pointee ownership
        // (`pts_to`) is carried by the general type-slprop lowering below.
        let domain = fnptr_domain_doc(arg_ty_docs.clone());

        let name_docs: Vec<Doc> = arg_names
            .iter()
            .map(|n| self.emit_name(Name::Var(n.val.clone())))
            .collect();

        // Bind each tuple component to its parameter name via projections
        // (rather than a `let (a,b) = x_fp` pattern match). Because the
        // projection form is definitionally equal to the corresponding
        // components — both here and in the wrapper body — the wrapper's proof
        // can connect `func_<g>`'s spec (over the bound names) to the tuple
        // `x_fp` without needing a tuple-reconstruction equation.
        //
        // The domain `fnptr_domain_doc` emits is a *flat* n-ary tuple: arity 1
        // is the bare type, arity 2 is `a & b` (`tuple2`, projected with
        // `fst`/`snd`), and arity >= 3 is `a & b & c ...` (`tupleN`, which is
        // NOT nested `tuple2`s, so `fst`/`snd` do not apply — use the `tupleN`
        // field projectors `MktupleN?._i`).
        let projs: Vec<Doc> = {
            let n = name_docs.len();
            (0..n)
                .map(|i| {
                    if n == 1 {
                        return Doc::text("x_fp");
                    }
                    if n == 2 {
                        let mut e = Doc::text("x_fp");
                        for _ in 0..i {
                            e = parens(Doc::text("snd ").append(e));
                        }
                        if i < n - 1 {
                            e = parens(Doc::text("fst ").append(e));
                        }
                        return e;
                    }
                    parens(Doc::text(format!("Mktuple{n}?._{} x_fp", i + 1)))
                })
                .collect()
        };

        // `let a = <proj0> in let b = <proj1> in ` prefix (empty for arity 0).
        let bind_prefix = |names: &[Doc]| -> Doc {
            Doc::concat(names.iter().zip(projs.iter()).map(|(name, proj)| {
                Doc::text("let ")
                    .append(name.clone())
                    .append(" = ")
                    .append(proj.clone())
                    .append(" in")
                    .append(Doc::hardline())
            }))
        };

        // Build requires/ensures slprops using the SAME general lowering as
        // `emit_fn_sig_inner` (ownership `pts_to`/`__pred` conjuncts for each
        // parameter plus the pure requires/ensures), so the wrapper body — a
        // direct call to `func_<g>` — verifies by a definitional match. Pointer
        // parameters thus carry their default `pts_to` permission across the
        // FuncPtr.
        let mut requires_props: Vec<Doc> = vec![];
        let mut ensures_props: Vec<Doc> = vec![];
        let mut preserves_props: Vec<Doc> = vec![];
        for (n, arg) in arg_names.iter().zip(decl.args.iter()) {
            match arg.mode {
                ParamMode::Regular | ParamMode::Consumed => {
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: false,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init {
                            perm: &Doc::text("1.0R"),
                        },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(n),
                    );
                    drop(naming);
                    if !type_props.is_empty() {
                        let wrapped = wrap_exists(&type_bindings, type_props);
                        match arg.mode {
                            ParamMode::Regular => {
                                requires_props.push(wrapped.clone());
                                ensures_props.push(wrapped);
                            }
                            ParamMode::Consumed => requires_props.push(wrapped),
                            _ => unreachable!(),
                        }
                    }
                }
                ParamMode::Const => {
                    let perm_name = self.emit_name(Name::Perm(extract_base_ident(&mk_rvar(n)), 0));
                    let perm_doc = Doc::text("'").append(perm_name);
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: true,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init { perm: &perm_doc },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(n),
                    );
                    drop(naming);
                    preserves_props.extend(type_props);
                }
                ParamMode::Out => {
                    let mut uninit_bindings = vec![];
                    let mut uninit_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: true,
                        bindings: &mut uninit_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Uninit,
                        &mut naming,
                        &mut uninit_props,
                        &mk_rvar(n),
                    );
                    drop(naming);
                    if !uninit_props.is_empty() {
                        requires_props.push(wrap_exists(&uninit_bindings, uninit_props));
                    }
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: false,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init {
                            perm: &Doc::text("1.0R"),
                        },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(n),
                    );
                    drop(naming);
                    if !type_props.is_empty() {
                        ensures_props.push(wrap_exists(&type_bindings, type_props));
                    }
                }
            }
        }
        // `preserves` (const params) hold across the call, so they belong in
        // both the pre and the post.
        requires_props.extend(preserves_props.iter().cloned());
        ensures_props.extend(preserves_props);

        // Conjoin the pure requires/ensures into single bool props. The post's
        // pure part is `req ==> ens`, not `ens`: the ensures is only guaranteed
        // when the precondition held, and stating it as an implication also
        // keeps partial operations in `ens` (e.g. `Int32.add`) well-defined,
        // since the inlined post `slprop` does not carry the precondition in
        // scope.
        let conj = |props: Vec<Doc>| -> Doc {
            if props.is_empty() {
                Doc::text("True")
            } else {
                parens(Doc::intersperse(
                    props.into_iter().map(parens),
                    Doc::text(" /\\ "),
                ))
            }
        };
        let req_props: Vec<Doc> = decl
            .requires
            .iter()
            .map(|r| self.emit_pure_prop(env, r))
            .collect();
        let has_req = !req_props.is_empty();
        let req_conj = conj(req_props);
        if has_req {
            requires_props.push(unaryfn(Doc::text("pure"), req_conj.clone()));
        }

        let return_id = env
            .push_return(decl.ret_type.clone())
            .with_loc(decl.ret_type.loc.clone());
        let ret_name = self.emit_name(Name::Var(return_id.val.clone()));
        let ret_ty_doc = self.emit_type(env, &decl.ret_type);
        {
            let mut ret_bindings = vec![];
            let mut ret_props = vec![];
            let mut naming = ValNaming::Standard {
                quote: false,
                bindings: &mut ret_bindings,
            };
            self.emit_type_slprop(
                env,
                &decl.ret_type,
                SLPropVariant::Init {
                    perm: &Doc::text("1.0R"),
                },
                &mut naming,
                &mut ret_props,
                &mk_rvar(&return_id),
            );
            drop(naming);
            if !ret_props.is_empty() {
                ensures_props.push(wrap_exists(&ret_bindings, ret_props));
            }
        }
        // Pure ensures reference the pointee value via the normal lowering.
        let ens_props_pure: Vec<Doc> = decl
            .ensures
            .iter()
            .map(|r| self.emit_pure_prop(env, r))
            .collect();
        if !ens_props_pure.is_empty() {
            let ens_conj = conj(ens_props_pure);
            let implied = if has_req {
                parens(req_conj.append(" ==> ").append(ens_conj))
            } else {
                ens_conj
            };
            ensures_props.push(unaryfn(Doc::text("pure"), implied));
        }

        let pre_body = mk_star(requires_props);
        let post_body = mk_star(ensures_props);

        let wrap_name = self.fnptr_wrap_name(&decl.name.val);
        let callee = self.emit_name(Name::Fn(decl.name.val.clone()));

        // Inline pre/post slprops (bound over the tuple domain `x_fp` via the
        // same projection prefix), to be spliced directly into the `__fp`
        // wrapper's `requires`/`ensures` instead of being named `unfold let`s.
        let pre_expr = parens(bind_prefix(&name_docs).append(pre_body));
        let post_expr = parens(bind_prefix(&name_docs).append(post_body));

        FnPtrSpecCore {
            pre_expr,
            post_expr,
            wrap_name,
            callee,
            domain,
            ret_name,
            ret_ty_doc,
            projs,
        }
    }

    /// Emit the fnptr triple for an address-taken function `g` in its own module.
    /// Returns `(fst_extra, fsti_extra)` (see `emit_fnptr_spec_core` for the
    /// shared pre/post generation).
    fn emit_fnptr_triple(&mut self, env: &Env, decl: &FnDecl) -> (Doc, Doc) {
        let FnPtrSpecCore {
            pre_expr,
            post_expr,
            wrap_name,
            callee,
            domain,
            ret_name,
            ret_ty_doc,
            projs,
        } = self.emit_fnptr_spec_core(env, decl);

        let wrap_kw = if decl.is_total {
            "fn "
        } else {
            "divergent fn "
        };
        let wrap_sig = Doc::text(wrap_kw)
            .append(wrap_name.clone())
            .append(" (x_fp: ")
            .append(domain.clone())
            .append(")")
            .append(Doc::hardline())
            .append("  requires ")
            .append(pre_expr.nest(2))
            .append(Doc::hardline())
            .append("  returns ")
            .append(ret_name.clone())
            .append(" : ")
            .append(ret_ty_doc)
            .append(Doc::hardline())
            .append("  ensures ")
            .append(post_expr.nest(2));

        let fsti = Doc::hardline()
            .append(Doc::hardline())
            .append(wrap_sig.clone());

        // fst: wrapper body delegates to `func_<g>`, passing each C parameter as
        // its tuple projection directly. Passing the projection (rather than a
        // `let`-bound copy) keeps the argument *definitionally* the tuple
        // component, which the prover needs to match ownership (`pts_to`)
        // preconditions carried by pointer-parameter callees.
        let call_body = match projs.len() {
            0 => callee.append(" ()"),
            _ => callee
                .append(" ")
                .append(Doc::intersperse(projs.iter().cloned(), Doc::text(" "))),
        };
        let fst = Doc::hardline()
            .append(Doc::hardline())
            .append(wrap_sig)
            .append(Doc::hardline())
            .append(Doc::text("{"))
            .append(Doc::hardline())
            .append(Doc::text("  ").append(call_body).nest(2))
            .append(Doc::hardline())
            .append(Doc::text("}"));

        (fst, fsti)
    }

    fn emit_fn_sig_for_interface(&mut self, env: &Env, decl: &FnDecl) -> Doc {
        self.emit_fn_sig_inner(env, decl, true)
    }

    fn emit_fn_sig_inner(
        &mut self,
        env: &Env,
        FnDecl {
            name,
            ret_type,
            args,
            ghost_args,
            requires,
            ensures,
            is_pure: _,
            is_rec,
            is_total,
            decreases,
        }: &FnDecl,
        for_interface: bool,
    ) -> Doc {
        let env = &mut env.clone();

        let mut requires_props = vec![];
        let mut ensures_props = vec![];
        let mut preserves_props = vec![];
        let mut params = vec![];

        // Emit ghost arguments as implicit erased parameters
        for ga in ghost_args {
            let var_name = annotated(&ga.name, || self.emit_name(Name::Var(ga.name.val.clone())));
            let ty_doc = self.emit_type(env, &ga.ty);
            params.push(parens(
                Doc::text("#")
                    .append(var_name)
                    .append(":")
                    .append(Doc::line())
                    .append(Doc::text("erased"))
                    .append(Doc::line())
                    .append(ty_doc),
            ));
            env.push_var_decl(&ga.name, ga.ty.clone(), LocalDeclKind::RValue);
        }

        for (i, arg) in args.iter().enumerate() {
            let n: Rc<Ident> = arg.name.clone().unwrap_or_else(|| {
                Rc::<str>::from(format!("_unnamed{}", i)).with_loc(arg.ty.loc.clone())
            });

            params.push(parens(
                annotated(&n, || self.emit_name(Name::Var(n.val.clone())))
                    .append(":")
                    .append(Doc::line())
                    .append(self.emit_type(env, &arg.ty)),
            ));

            env.push_arg(arg, LocalDeclKind::RValue);
            match arg.mode {
                ParamMode::Regular | ParamMode::Consumed => {
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: false,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init {
                            perm: &Doc::text("1.0R"),
                        },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(&n),
                    );
                    drop(naming);
                    if !type_props.is_empty() {
                        let wrapped = wrap_exists(&type_bindings, type_props);
                        match arg.mode {
                            ParamMode::Regular => {
                                requires_props.push(wrapped.clone());
                                ensures_props.push(wrapped);
                            }
                            ParamMode::Consumed => {
                                requires_props.push(wrapped);
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                ParamMode::Const => {
                    let perm_name = self.emit_name(Name::Perm(extract_base_ident(&mk_rvar(&n)), 0));
                    let perm_doc = Doc::text("'").append(perm_name);
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: true,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init { perm: &perm_doc },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(&n),
                    );
                    drop(naming);
                    preserves_props.extend(type_props);
                }
                ParamMode::Out => {
                    // Precondition: uninit slprop
                    let mut uninit_bindings = vec![];
                    let mut uninit_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: true,
                        bindings: &mut uninit_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Uninit,
                        &mut naming,
                        &mut uninit_props,
                        &mk_rvar(&n),
                    );
                    drop(naming);
                    if !uninit_props.is_empty() {
                        requires_props.push(wrap_exists(&uninit_bindings, uninit_props));
                    }

                    // Postcondition: normal initialized slprop
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: false,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init {
                            perm: &Doc::text("1.0R"),
                        },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(&n),
                    );
                    drop(naming);
                    if !type_props.is_empty() {
                        ensures_props.push(wrap_exists(&type_bindings, type_props));
                    }
                }
            }
        }

        if params.is_empty() {
            params.push(Doc::text("()"));
        }

        requires_props.extend(requires.iter().map(|r| self.emit_rvalue(env, r)));

        let return_id = env
            .push_return(ret_type.clone())
            .with_loc(ret_type.loc.clone());
        let mut ret_bindings = vec![];
        let mut ret_props = vec![];
        let mut naming = ValNaming::Standard {
            quote: false,
            bindings: &mut ret_bindings,
        };
        self.emit_type_slprop(
            env,
            &ret_type,
            SLPropVariant::Init {
                perm: &Doc::text("1.0R"),
            },
            &mut naming,
            &mut ret_props,
            &mk_rvar(&return_id),
        );
        drop(naming);
        if !ret_props.is_empty() {
            ensures_props.push(wrap_exists(&ret_bindings, ret_props));
        }
        let ret_type_doc = self.emit_type(env, ret_type);

        ensures_props.extend(ensures.iter().map(|r| self.emit_rvalue(env, r)));

        // C functions are not guaranteed to terminate, and PAL emits `while`
        // loops without a `decreases` measure. Since Pulse split `stt` into a
        // terminating `stt` (`fn`) and a possibly-divergent `stt_div`
        // (`divergent fn`), such loops (and their callers) must live in the
        // divergent effect. We therefore default every emitted function to
        // `divergent`; a divergent computation may still call terminating ones.
        // The `_total` annotation opts a function back into termination
        // checking, emitting a plain `fn` (which then requires any `while` loop
        // or recursion to be well-founded).
        let divergent = if *is_total {
            Doc::nil()
        } else {
            Doc::text("divergent ")
        };
        let fn_keyword = if *is_rec {
            divergent.append(Doc::text("fn rec"))
        } else {
            divergent.append(Doc::text("fn"))
        };

        let hdr = Doc::group(
            fn_keyword
                .append(Doc::line())
                .append(self.emit_name(Name::Fn(name.val.clone()))),
        )
        .append(Doc::concat(params.into_iter().map(|p| Doc::line().append(p))).nest(2))
        .group();

        hdr.append(Doc::concat(requires_props.into_iter().map(|r| {
            Doc::hardline().append(
                Doc::text("requires")
                    .append(Doc::line())
                    .append(r)
                    .nest(2)
                    .group(),
            )
        })))
        .append(Doc::concat(preserves_props.into_iter().map(|r| {
            Doc::hardline().append(
                Doc::text("preserves")
                    .append(Doc::line())
                    .append(r)
                    .nest(2)
                    .group(),
            )
        })))
        .append(Doc::hardline())
        .append(Doc::group(
            Doc::text("returns")
                .append(Doc::line())
                .append(self.emit_name(Name::Var(return_id.val.clone())))
                .append(Doc::line())
                .append(":")
                .group()
                .append(Doc::line())
                .append(ret_type_doc),
        ))
        .append(Doc::concat(ensures_props.into_iter().map(|r| {
            Doc::hardline().append(
                Doc::text("ensures")
                    .append(Doc::line())
                    .append(r)
                    .nest(2)
                    .group(),
            )
        })))
        .append(if for_interface {
            Doc::nil()
        } else {
            match decreases {
                Some(dec) => Doc::hardline().append(
                    Doc::text("decreases")
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, dec))
                        .nest(2)
                        .group(),
                ),
                None => Doc::nil(),
            }
        })
        .group()
    }

    fn emit_fn_decl(&mut self, env: &Env, decl: &FnDecl) -> Doc {
        self.emit_fn_sig(env, decl)
            .nest(2)
            .append(Doc::hardline())
            // add a (warning-free) body so that we can call it
            .append("{ assume pure False; unreachable () }")
    }

    fn emit_fn_defn(&mut self, env: &Env, FnDefn { decl, body }: &FnDefn) -> Doc {
        if decl.is_pure {
            return self.emit_pure_fn(env, decl, body);
        }
        self.current_fn_total = decl.is_total;
        let decl_doc = self.emit_fn_sig(env, decl).nest(2).append(Doc::hardline());
        let arg_redecl_as_mut = Doc::concat(decl.args.iter().filter_map(|arg| {
            arg.name.as_ref().map(|n| {
                Doc::line().append(annotated(n, || {
                    Doc::group({
                        let n = self.emit_name(Name::Var(n.val.clone()));
                        Doc::text("let mut ")
                            .append(n.clone())
                            .append(" = ")
                            .append(n)
                            .append(";")
                    })
                }))
            })
        }));
        let env = &mut env.clone();
        env.push_fn_decl_args_for_body(decl);
        decl_doc.append(block(arg_redecl_as_mut.append(self.emit_stmts(env, body))).group())
    }
} // impl Emitter (group E)

/// Append remaining statements to a block (for if/else continuation in pure functions).
fn append_rest(block_stmts: &[Rc<Stmt>], rest: &[Rc<Stmt>]) -> Vec<Rc<Stmt>> {
    block_stmts.iter().chain(rest.iter()).cloned().collect()
}

impl<'a> Emitter<'a> {
    /// Emit a pure function spec prop: strip the outer Cast(_, SLProp) wrapper
    /// and emit the inner boolean expression directly.
    fn emit_pure_prop(&mut self, env: &Env, expr: &Expr) -> Doc {
        match &expr.val {
            ExprT::Cast(inner, ty) if matches!(ty.val, TypeT::SLProp) => {
                self.emit_rvalue(env, inner)
            }
            _ => self.emit_rvalue(env, expr),
        }
    }

    /// Emit an expression as a standalone `slprop` term (e.g. the body of a
    /// `_slprop` `_let`). Unlike the Pulse-block `with_pure` sugar, a plain F*
    /// term must use the `pure` constructor to lift a boolean prop into `slprop`.
    fn emit_slprop_term(&mut self, env: &Env, expr: &Expr) -> Doc {
        match &expr.val {
            ExprT::Cast(inner, ty) if matches!(ty.val, TypeT::SLProp) => {
                unaryfn(Doc::text("pure"), self.emit_rvalue(env, inner))
            }
            _ => self.emit_rvalue(env, expr),
        }
    }

    /// Check that a parameter type is valid for a pure function (no pointers, arrays, etc.)
    fn check_pure_type(&mut self, ty: &Type) {
        match &ty.val {
            TypeT::Void
            | TypeT::Bool
            | TypeT::Int { .. }
            | TypeT::Float { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::SpecInt
            | TypeT::SpecNat
            | TypeT::SLProp
            | TypeT::Unknown
            | TypeT::Error
            | TypeT::TypeRef(_) => {}
            TypeT::Pointer(_, _) => {
                self.report(
                    format!("pointer parameters are not supported in pure functions"),
                    &ty.loc,
                );
            }
            TypeT::FixedArray(_, _) => {
                self.report(
                    format!("array parameters are not supported in pure functions"),
                    &ty.loc,
                );
            }
            TypeT::FlexArray(_) => {
                self.report(
                    format!("flexible array members are not supported in pure functions"),
                    &ty.loc,
                );
            }
            TypeT::FnPtr { .. } => {
                self.report(
                    format!("function-pointer parameters are not supported in pure functions"),
                    &ty.loc,
                );
            }
            TypeT::Refine(inner, _)
            | TypeT::RefineAlways(inner, _)
            | TypeT::RefineUninit(inner, _)
            | TypeT::RefineValue(inner, ..)
            | TypeT::Plain(inner)
            | TypeT::Nullable(inner) => self.check_pure_type(inner),
        }
    }

    fn emit_pure_body(&mut self, env: &Env, stmts: &[Rc<Stmt>]) -> Doc {
        if stmts.is_empty() {
            return Doc::text("()");
        }

        match &stmts[0].val {
            StmtT::Return(Some(e)) if stmts.len() == 1 => self.emit_rvalue(env, e),
            StmtT::Return(None) if stmts.len() == 1 => Doc::text("()"),

            StmtT::If {
                cond,
                then_branch: then_body,
                else_branch: else_body,
                ..
            } => {
                let rest = &stmts[1..];
                let then_stmts = append_rest(then_body, rest);
                let else_stmts = append_rest(else_body, rest);
                let mut env_then = env.clone();
                for s in &**then_body {
                    env_then.push_stmt(s);
                }
                let mut env_else = env.clone();
                for s in &**else_body {
                    env_else.push_stmt(s);
                }
                parens(
                    Doc::text("if")
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, cond))
                        .group()
                        .append(Doc::line())
                        .append("then")
                        .append(
                            Doc::line()
                                .append(self.emit_pure_body(&env_then, &then_stmts))
                                .nest(2),
                        )
                        .append(Doc::line())
                        .append("else")
                        .append(
                            Doc::line()
                                .append(self.emit_pure_body(&env_else, &else_stmts))
                                .nest(2),
                        ),
                )
            }

            StmtT::GhostStmt(code) => {
                let env = &mut env.clone();
                let ghost_doc = self.emit_inline_pulse_tokens(env, code);
                let rest = self.emit_pure_body(env, &stmts[1..]);
                parens(
                    Doc::text("let")
                        .append(Doc::line())
                        .append("_")
                        .append(Doc::line())
                        .append("=")
                        .group()
                        .nest(2)
                        .append(Doc::line().append(ghost_doc).nest(2))
                        .append(Doc::line())
                        .append("in")
                        .append(Doc::line().append(rest).nest(2)),
                )
            }

            StmtT::Match {
                scrutinee,
                branches,
                default_branch,
                ..
            } => {
                let rest = &stmts[1..];
                let mut branch_docs = Vec::new();
                for branch in &**branches {
                    for pattern in &*branch.patterns {
                        let branch_stmts = append_rest(&branch.body, rest);
                        branch_docs.push(
                            Doc::line()
                                .append("| ")
                                .append(self.emit_pattern(env, pattern))
                                .append(" ->")
                                .append(
                                    Doc::line()
                                        .append(self.emit_pure_body(env, &branch_stmts))
                                        .nest(2),
                                ),
                        );
                    }
                }
                parens(
                    Doc::text("match")
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, scrutinee))
                        .append(Doc::line())
                        .append("with")
                        .append(Doc::concat(branch_docs))
                        .append(Doc::line())
                        .append("| _ ->")
                        .append(
                            Doc::line()
                                .append(
                                    self.emit_pure_body(env, &append_rest(default_branch, rest)),
                                )
                                .nest(2),
                        ),
                )
            }

            StmtT::Let(x, ty, value) => {
                let value_doc = self.emit_rvalue(env, value);
                let ty_doc = self.emit_type(env, ty);
                let mut rest_env = env.clone();
                rest_env.push_var_decl(x, ty.clone(), LocalDeclKind::RValue);
                let rest = self.emit_pure_body(&rest_env, &stmts[1..]);
                parens(
                    Doc::text("let")
                        .append(Doc::line())
                        .append(self.emit_name(Name::Var(x.val.clone())))
                        .append(Doc::line())
                        .append(":")
                        .append(Doc::line())
                        .append(ty_doc)
                        .append(Doc::line())
                        .append("=")
                        .group()
                        .nest(2)
                        .append(Doc::line().append(value_doc).nest(2))
                        .append(Doc::line())
                        .append("in")
                        .append(Doc::line().append(rest).nest(2)),
                )
            }

            StmtT::Decl(x, ty) => {
                // Look for the assignment to this variable in the next statement
                if stmts.len() >= 3 {
                    if let StmtT::Assign(lhs, rhs) = &stmts[1].val {
                        if let ExprT::Var(v) = &lhs.val {
                            if v.val == x.val {
                                let mut env = env.clone();
                                env.push_var_decl(x, ty.clone(), LocalDeclKind::RValue);
                                let rest_expr = self.emit_pure_body(&env, &stmts[2..]);
                                return parens(
                                    Doc::text("let")
                                        .append(Doc::line())
                                        .append(self.emit_name(Name::Var(x.val.clone())))
                                        .append(Doc::line())
                                        .append(":")
                                        .append(Doc::line())
                                        .append(self.emit_type(&env, ty))
                                        .append(Doc::line())
                                        .append("=")
                                        .group()
                                        .nest(2)
                                        .append(
                                            Doc::line().append(self.emit_rvalue(&env, rhs)).nest(2),
                                        )
                                        .append(Doc::line())
                                        .append("in")
                                        .append(Doc::line().append(rest_expr).nest(2)),
                                );
                            }
                        }
                    }
                }
                self.report(
                    format!("unsupported declaration without assignment in pure function"),
                    &stmts[0].loc,
                );
                Doc::text("(admit())")
            }

            _ => {
                self.report(
                    format!("unsupported statement in pure function: {}", stmts[0]),
                    &stmts[0].loc,
                );
                Doc::text("(admit())")
            }
        }
    }

    fn emit_pure_fn(&mut self, env: &Env, decl: &FnDecl, body: &Stmts) -> Doc {
        let env = &mut env.clone();

        let mut params = vec![];

        // Emit ghost arguments as implicit erased parameters
        for ga in &decl.ghost_args {
            let var_name = annotated(&ga.name, || self.emit_name(Name::Var(ga.name.val.clone())));
            let ty_doc = self.emit_type(env, &ga.ty);
            params.push(parens(
                Doc::text("#")
                    .append(var_name)
                    .append(":")
                    .append(Doc::line())
                    .append(Doc::text("erased"))
                    .append(Doc::line())
                    .append(ty_doc),
            ));
            env.push_var_decl(&ga.name, ga.ty.clone(), LocalDeclKind::RValue);
        }

        for (i, arg) in decl.args.iter().enumerate() {
            let n: Rc<Ident> = arg.name.clone().unwrap_or_else(|| {
                Rc::<str>::from(format!("_unnamed{}", i)).with_loc(arg.ty.loc.clone())
            });

            params.push(parens(
                annotated(&n, || self.emit_name(Name::Var(n.val.clone())))
                    .append(":")
                    .append(Doc::line())
                    .append(self.emit_type(env, &arg.ty)),
            ));

            env.push_arg(arg, LocalDeclKind::RValue);
        }

        if params.is_empty() {
            params.push(Doc::text("()"));
        }

        let requires_props: Vec<Doc> = decl
            .requires
            .iter()
            .map(|r| self.emit_pure_prop(env, r))
            .collect();
        // Reject non-bool type-level specs on parameters
        for arg in &decl.args {
            self.check_pure_type(&arg.ty);
        }

        let ret_type_doc = self.emit_type(env, &decl.ret_type);

        let return_id = env
            .push_return(decl.ret_type.clone())
            .with_loc(decl.ret_type.loc.clone());
        let ensures_props: Vec<Doc> = decl
            .ensures
            .iter()
            .map(|e| self.emit_pure_prop(env, e))
            .collect();

        let body_doc = self.emit_pure_body(env, body);

        let has_specs = !requires_props.is_empty() || !ensures_props.is_empty();

        let ty_doc = if has_specs || (decl.is_rec && decl.decreases.is_some()) {
            let req_doc = if requires_props.is_empty() {
                Doc::text("True")
            } else {
                Doc::intersperse(requires_props, Doc::text(" /\\ "))
            };
            let ens_doc = if ensures_props.is_empty() {
                Doc::text("True")
            } else {
                Doc::intersperse(ensures_props, Doc::text(" /\\ "))
            };
            let mut pure_args = vec![
                Doc::text("Pure"),
                ret_type_doc,
                parens(Doc::text("requires").append(Doc::line()).append(req_doc)),
                parens(
                    Doc::text("ensures").append(Doc::line()).append(parens(
                        Doc::text("fun")
                            .append(Doc::line())
                            .append(self.emit_name(Name::Var(return_id.val.clone())))
                            .append(Doc::line())
                            .append("->")
                            .group()
                            .nest(2)
                            .append(Doc::line())
                            .append(ens_doc),
                    )),
                ),
            ];
            if let Some(decreases_expr) = &decl.decreases {
                pure_args.push(parens(
                    Doc::text("decreases")
                        .append(Doc::line())
                        .append(self.emit_rvalue(env, decreases_expr)),
                ));
            }
            naryfn(pure_args)
        } else {
            ret_type_doc
        };

        let body = mk_let_rec(
            decl.is_rec,
            self.emit_name(Name::Fn(decl.name.val.clone())),
            &params,
            ty_doc,
            body_doc,
        );
        body
    }

    fn emit_let_decl(&mut self, env: &Env, let_decl: &LetDecl) -> Doc {
        if let_decl.is_impure {
            return self.emit_letimpure_decl(env, let_decl);
        }

        let env = &mut env.clone();

        let mut params = vec![];
        for (i, arg) in let_decl.params.iter().enumerate() {
            let n: Rc<Ident> = arg.name.clone().unwrap_or_else(|| {
                Rc::<str>::from(format!("_unnamed{}", i)).with_loc(arg.ty.loc.clone())
            });

            params.push(parens(
                annotated(&n, || self.emit_name(Name::Var(n.val.clone())))
                    .append(":")
                    .append(Doc::line())
                    .append(self.emit_type(env, &arg.ty)),
            ));

            env.push_arg(arg, LocalDeclKind::RValue);
        }

        if params.is_empty() {
            params.push(Doc::text("()"));
        }

        let requires_props: Vec<Doc> = let_decl
            .requires
            .iter()
            .map(|r| self.emit_pure_prop(env, r))
            .collect();
        let ret_type_doc = self.emit_type(env, &let_decl.ret_type);

        let return_id = env
            .push_return(let_decl.ret_type.clone())
            .with_loc(let_decl.ret_type.loc.clone());
        let ensures_props: Vec<Doc> = let_decl
            .ensures
            .iter()
            .map(|e| self.emit_pure_prop(env, e))
            .collect();

        let has_specs = !requires_props.is_empty() || !ensures_props.is_empty();

        let ty_doc = if has_specs {
            let req_doc = if requires_props.is_empty() {
                Doc::text("True")
            } else {
                Doc::intersperse(requires_props, Doc::text(" /\\ "))
            };
            let ens_doc = if ensures_props.is_empty() {
                Doc::text("True")
            } else {
                Doc::intersperse(ensures_props, Doc::text(" /\\ "))
            };
            naryfn(vec![
                Doc::text("Ghost"),
                ret_type_doc,
                parens(Doc::text("requires").append(Doc::line()).append(req_doc)),
                parens(
                    Doc::text("ensures").append(Doc::line()).append(parens(
                        Doc::text("fun")
                            .append(Doc::line())
                            .append(self.emit_name(Name::Var(return_id.val.clone())))
                            .append(Doc::line())
                            .append("->")
                            .group()
                            .nest(2)
                            .append(Doc::line())
                            .append(ens_doc),
                    )),
                ),
            ])
        } else {
            unaryfn(Doc::text("GTot"), ret_type_doc)
        };

        let body_doc = if matches!(let_decl.ret_type.val, TypeT::SLProp) {
            self.emit_slprop_term(env, &let_decl.body)
        } else {
            self.emit_rvalue(env, &let_decl.body)
        };

        let body = mk_let_rec(
            let_decl.is_rec,
            self.emit_name(Name::Fn(let_decl.name.val.clone())),
            &params,
            ty_doc,
            body_doc,
        );
        body
    }

    fn emit_letimpure_decl(&mut self, env: &Env, let_decl: &LetDecl) -> Doc {
        let env = &mut env.clone();

        let mut requires_props = vec![];
        let mut params = vec![];

        for (i, arg) in let_decl.params.iter().enumerate() {
            let n: Rc<Ident> = arg.name.clone().unwrap_or_else(|| {
                Rc::<str>::from(format!("_unnamed{}", i)).with_loc(arg.ty.loc.clone())
            });

            params.push(parens(
                annotated(&n, || {
                    Doc::text(self.nm.mangle(&Name::Var(n.val.clone())).to_string())
                })
                .append(":")
                .append(Doc::line())
                .append(self.emit_type(env, &arg.ty)),
            ));

            env.push_arg(arg, LocalDeclKind::RValue);
            match arg.mode {
                ParamMode::Const => {
                    let perm_name = Doc::text(
                        self.nm
                            .mangle(&Name::Perm(extract_base_ident(&mk_rvar(&n)), 0))
                            .to_string(),
                    );
                    let perm_doc = Doc::text("'").append(perm_name);
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: true,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init { perm: &perm_doc },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(&n),
                    );
                    drop(naming);
                    requires_props.extend(type_props);
                }
                _ => {
                    let mut type_bindings = vec![];
                    let mut type_props = vec![];
                    let mut naming = ValNaming::Standard {
                        quote: false,
                        bindings: &mut type_bindings,
                    };
                    self.emit_type_slprop(
                        env,
                        &arg.ty,
                        SLPropVariant::Init {
                            perm: &Doc::text("1.0R"),
                        },
                        &mut naming,
                        &mut type_props,
                        &mk_rvar(&n),
                    );
                    drop(naming);
                    if !type_props.is_empty() {
                        requires_props.push(wrap_exists(&type_bindings, type_props));
                    }
                }
            }
        }

        if params.is_empty() {
            params.push(Doc::text("()"));
        }

        let ret_type_doc = self.emit_type(env, &let_decl.ret_type);
        let return_id = env
            .push_return(let_decl.ret_type.clone())
            .with_loc(let_decl.ret_type.loc.clone());

        // Build the rewrites_to ensures clause: rewrites_to return_id (old (body_expr))
        let body_rvalue = self.emit_rvalue(env, &let_decl.body);
        let rewrites_to_doc = Doc::text("rewrites_to")
            .append(Doc::line())
            .append(Doc::text(
                self.nm
                    .mangle(&Name::Var(return_id.val.clone()))
                    .to_string(),
            ))
            .append(Doc::line())
            .append(parens(
                Doc::text("old").append(Doc::line()).append(body_rvalue),
            ));

        // Header: ghost fn name (params)
        let hdr = Doc::group(
            Doc::text("ghost fn").append(Doc::line()).append(Doc::text(
                self.nm
                    .mangle(&Name::Fn(let_decl.name.val.clone()))
                    .to_string(),
            )),
        )
        .append(Doc::concat(params.into_iter().map(|p| Doc::line().append(p))).nest(2))
        .group();

        let sig = hdr
            .append(Doc::concat(requires_props.into_iter().map(|r| {
                Doc::hardline().append(
                    Doc::text("requires")
                        .append(Doc::line())
                        .append(r)
                        .nest(2)
                        .group(),
                )
            })))
            // requires pure False
            .append(Doc::hardline())
            .append(
                Doc::text("requires")
                    .append(Doc::line())
                    .append("pure False")
                    .nest(2)
                    .group(),
            )
            .append(Doc::hardline())
            .append(Doc::group(
                Doc::text("returns")
                    .append(Doc::line())
                    .append(Doc::text(
                        self.nm
                            .mangle(&Name::Var(return_id.val.clone()))
                            .to_string(),
                    ))
                    .append(Doc::line())
                    .append(":")
                    .group()
                    .append(Doc::line())
                    .append(ret_type_doc),
            ))
            // ensures rewrites_to ...
            .append(Doc::hardline())
            .append(
                Doc::text("ensures")
                    .append(Doc::line())
                    .append(rewrites_to_doc)
                    .nest(2)
                    .group(),
            )
            .group();

        sig.nest(2)
            .append(Doc::hardline())
            .append("{ unreachable () }")
    }

    fn emit_global_var(&mut self, env: &Env, gv: &GlobalVar) -> Doc {
        if !gv.is_pure {
            self.report(
                "non-pure global variables are not yet supported".to_string(),
                &gv.name.loc,
            );
            return Doc::nil();
        }
        let name = self.emit_name(Name::Var(gv.name.val.clone()));
        let ty = self.emit_type(env, &gv.ty);
        let body = match &gv.init {
            Some(init) => self.emit_rvalue(env, init),
            None => self.emit_type_default(env, &gv.ty),
        };
        let def = mk_let(name.clone(), &[], ty, body);
        let def = if gv.opaque_to_smt {
            Doc::text("[@@\"opaque_to_smt\"]")
                .append(Doc::hardline())
                .append(def)
        } else {
            def
        };
        match self.emit_global_addr(env, gv) {
            Some(addr) => def.append(Doc::hardline()).append(addr),
            None => def,
        }
    }

    /// Emit a `_pure` global's address: an assumed `ref` (one per global, so
    /// distinct globals get distinct addresses), a non-null axiom, and the
    /// acquire that hands out *read-only* ownership of its storage.
    ///
    /// Reads of a `_pure` global are ownership-free, which is only sound if the
    /// storage holds `var_g` forever -- so the pointer must never be writable.
    /// Hiding the permission under an existential achieves that, and it must
    /// stay existential rather than some fixed fraction `k`: `k` acquired `n`
    /// times gathers to `n * k`, and `pts_to_perm_bound` (`p <=. 1.0R`) would
    /// then prove `False` for `n > 1/k`.
    ///
    /// The `pts_to` is emitted literally, not behind an abbreviation: Pulse's
    /// `[@@pulse_intro] __aux_raw_unfold` only fires on a literal `pts_to`,
    /// which the struct-global case depends on.
    ///
    /// The acquire is an `assume val` rather than an admitted `ghost fn`: the
    /// ownership is *assumed* to exist, being a fraction of the one reserved
    /// for the global at program start. Callers release it with `drop_`.
    ///
    /// Emitted for every eligible global, whether or not its address is taken
    /// (the `&g` may live in another module), as for the `__fp` wrappers.
    /// See `doc/pal_surface_syntax.md`.
    fn emit_global_addr(&mut self, env: &Env, gv: &GlobalVar) -> Option<Doc> {
        if global_var_is_array(gv) {
            return None;
        }
        let var = self.emit_name(Name::Var(gv.name.val.clone()));
        let addr = self.emit_name(Name::GlobalAddr(gv.name.val.clone()));
        let ty = self.emit_type(env, &gv.ty);
        let ref_ty = parens(Doc::text("ref").append(Doc::line()).append(ty).nest(2));

        let addr_val = Doc::text("assume val ")
            .append(addr.clone())
            .append(Doc::text(" : "))
            .append(ref_ty.clone());
        let not_null = Doc::text("assume val ")
            .append(self.emit_name(Name::GlobalAddrNotNull(gv.name.val.clone())))
            .append(Doc::text(" : squash (~(Pulse.Lib.Reference.is_null "))
            .append(addr.clone())
            .append(Doc::text("))"));
        let perm = Doc::text("p");
        let pts_to = naryfn([
            Doc::text("Pulse.Lib.Reference.pts_to"),
            addr,
            Doc::text("#").append(perm.clone()),
            var,
        ]);
        let addr_of = mk_assume_val(
            vec![],
            self.emit_name(Name::GlobalAcquire(gv.name.val.clone())),
            &[],
            naryfn([
                Doc::text("unit"),
                Doc::text("->"),
                Doc::text("stt_ghost"),
                Doc::text("unit"),
                Doc::text("emp_inames"),
                Doc::text("emp"),
                mk_thunk(wrap_exists(
                    &[ExBinding {
                        name: perm,
                        ty: Doc::text("perm"),
                    }],
                    vec![pts_to],
                )),
            ]),
        );

        Some(
            addr_val
                .append(Doc::hardline())
                .append(not_null)
                .append(Doc::hardline())
                .append(addr_of),
        )
    }

    fn emit_decl(&mut self, env: &Env, decl: &Decl) -> Doc {
        annotated(decl, || match &decl.val {
            DeclT::FnDefn(fn_defn) => self.emit_fn_defn(env, fn_defn),
            DeclT::FnDecl(fn_decl) => self.emit_fn_decl(env, fn_decl),
            DeclT::Typedef(typedef) => self.emit_typedef(env, typedef),
            DeclT::StructDefn(struct_defn) => self.emit_structdefn(env, struct_defn),
            DeclT::StructDecl(name) => self.emit_struct_decl(env, name),
            DeclT::UnionDefn(union_defn) => self.emit_uniondefn(env, union_defn),
            DeclT::IncludeDecl(include_decl) => {
                let env = &mut env.clone();
                self.emit_inline_pulse_tokens(env, &include_decl.code)
            }
            DeclT::LetDecl(let_decl) => self.emit_let_decl(env, let_decl),
            DeclT::OpaqueTypeDecl(decl) => {
                let env = &mut env.clone();
                let t = self.emit_name(Name::TypeRef(TypeRef::Typedef(decl.name.val.clone())));
                Doc::text("unfold").append(Doc::line()).append(mk_let(
                    t,
                    &[],
                    Doc::text("Type"),
                    self.emit_inline_pulse_tokens(env, &decl.code),
                ))
            }
            DeclT::GlobalVar(gv) => self.emit_global_var(env, gv),
        })
    }
} // impl Emitter (group F)

/// Emitted output for a single module.
pub struct EmittedModule {
    pub module_name: String,
    pub code: String,
    pub fsti_code: Option<String>,
    pub range_map: SourceRangeMap,
    pub source_file: Rc<str>,
    pub decl_name: String,
    pub decl_range: Range,
}

/// Emit each declaration as its own module.
/// Returns a list of (module_name, code, source_range_map) for each declaration.
pub fn emit_multifile(diags: &mut Diagnostics, tu: &TranslationUnit) -> Vec<EmittedModule> {
    // Build env with all decls pre-registered so call sites can resolve forward
    // references regardless of source order. PAL's clang frontend does not always
    // visit decls in source order (e.g. functions defined later in a TU may be
    // emitted before functions defined earlier), so incremental population would
    // cause `infer_expr` to fail on later-defined callees, producing wrong code
    // in `BinOp::Eq` (`= array_null` instead of `array_is_null ...`) and other
    // type-driven emit branches.
    let mut full_env = Env::new();
    for decl in &tu.decls {
        full_env.push_decl(decl);
    }

    // Build the map from function/let/global identifiers to their owning modules
    let fn_module_map = build_fn_module_map(&tu.decls);
    // Build the override map for OpaqueTypeDecl typedef names
    let typedef_override_map = build_typedef_override_map(&tu.decls);

    let mut results = Vec::new();

    // Emit all modules, collecting code bodies
    struct PendingModule {
        mod_name: String,
        body_code: String,
        fsti_body_code: Option<String>,
        range_map: crate::pass::emit::SourceRangeMap,
        source_file: Rc<str>,
        decl_name: String,
        decl_range: Range,
    }

    let mut pending: Vec<PendingModule> = Vec::new();
    // Track already-emitted module names to skip duplicate declarations
    // (e.g., forward typedef + full typedef for the same name).
    // We keep the LAST occurrence (most complete definition).
    let mut seen_modules: HashMap<String, usize> = HashMap::new();

    let env = full_env;
    // Reuse a single Emitter across all modules
    let mut emitter = Emitter {
        nm: NameMangling::new(),
        diags,
        type_val_params: HashMap::new(),
        type_uninit_val_params: HashMap::new(),
        defining_struct: None,
        current_module: String::new(),
        fn_module_map,
        typedef_override_map,
        current_fn_total: false,
        tmp_counter: 0,
    };

    let addr_taken = collect_addr_taken(&tu.decls);

    for decl in &tu.decls {
        let mod_name = module_name_for_decl(decl);
        emitter.current_module = mod_name.clone();

        // Emit just the body (decl code)
        let body_doc = emitter.emit_decl(&env, decl);
        let mut writer = StrWriter::new();
        body_doc.render_raw(100, &mut writer).unwrap();

        // For function definitions, also emit the interface (signature only, no body)
        // Skip pure functions — they are emitted as `let` definitions, not `fn`
        let fsti_body_code = if let DeclT::FnDefn(fn_defn) = &decl.val {
            if fn_defn.decl.is_pure {
                None
            } else {
                let iface_doc = emitter.emit_fn_sig_for_interface(&env, &fn_defn.decl);
                let mut iface_writer = StrWriter::new();
                iface_doc.render_raw(100, &mut iface_writer).unwrap();
                Some(iface_writer.buffer)
            }
        } else {
            None
        };

        let decl_loc = decl.loc.location();
        let new_module = PendingModule {
            mod_name: mod_name.clone(),
            body_code: writer.buffer,
            fsti_body_code,
            range_map: writer.source_range_map,
            source_file: decl_loc.file_name.clone(),
            decl_name: decl_name(decl),
            decl_range: decl_loc.range,
        };

        // Deduplicate: if we've seen this module name before, replace with the later (more complete) one
        if let Some(&idx) = seen_modules.get(&mod_name) {
            pending[idx] = new_module;
        } else {
            seen_modules.insert(mod_name.clone(), pending.len());
            pending.push(new_module);
        }

        // For an address-taken function, emit its fnptr triple as its own module
        // `Funcptr_<g>`: the wrapper implementation goes in the `.fst`, the
        // `pre`/`post` definitions and wrapper signature go in the `.fsti`. The
        // wrapper body's `func_<g>` reference qualifies to `Func_<g>.func_<g>`
        // because `current_module` is the fnptr module while emitting.
        // A declaration gets one too: its `Func_<g>` stub carries the declared
        // contract for the wrapper body to delegate to. `merge` drops a `FnDecl`
        // that has a matching `FnDefn`, so only one arm fires per function.
        let wrapper_decl: Option<&FnDecl> = match &decl.val {
            DeclT::FnDefn(fn_defn) => Some(&fn_defn.decl),
            DeclT::FnDecl(fn_decl) => Some(fn_decl),
            _ => None,
        };
        if let Some(fn_decl) = wrapper_decl {
            if !fn_decl.is_pure && addr_taken.contains(&fn_decl.name.val) {
                let fp_mod = funcptr_module_name(&fn_decl.name.val);
                emitter.current_module = fp_mod.clone();
                let (fst_extra, fsti_extra) = emitter.emit_fnptr_triple(&env, fn_decl);

                let mut fp_writer = StrWriter::new();
                fst_extra.render_raw(100, &mut fp_writer).unwrap();
                let mut fp_fsti_writer = StrWriter::new();
                fsti_extra.render_raw(100, &mut fp_fsti_writer).unwrap();

                let fp_module = PendingModule {
                    mod_name: fp_mod.clone(),
                    body_code: fp_writer.buffer,
                    fsti_body_code: Some(fp_fsti_writer.buffer),
                    range_map: fp_writer.source_range_map,
                    source_file: decl_loc.file_name.clone(),
                    decl_name: decl_name(decl),
                    decl_range: decl_loc.range,
                };

                if let Some(&idx) = seen_modules.get(&fp_mod) {
                    pending[idx] = fp_module;
                } else {
                    seen_modules.insert(fp_mod, pending.len());
                    pending.push(fp_module);
                }
            }
        }
    }

    // Build final code with preambles
    for pm in pending {
        let preamble = format!(
            "module {}\nopen Pulse\nopen Pulse.Lib.C\n#lang-pulse\n\n",
            pm.mod_name
        );
        let full_code = format!("{}{}", preamble, pm.body_code);
        let fsti_code = pm
            .fsti_body_code
            .map(|body| format!("{}{}", preamble, body));

        results.push(EmittedModule {
            module_name: pm.mod_name,
            code: full_code,
            fsti_code,
            range_map: pm.range_map,
            source_file: pm.source_file,
            decl_name: pm.decl_name,
            decl_range: pm.decl_range,
        });
    }

    results
}
