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
        Name::UnionFieldConstructor(u, _) => Some(format!("Union_{}", u)),
        Name::UnionGhostFieldProj(u, _) => Some(format!("Union_{}", u)),
        Name::UnionFieldProj(u, _) => Some(format!("Union_{}", u)),
        Name::UnionAuxFn(u, _, _) => Some(format!("Union_{}", u)),
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
                map.insert(
                    fn_defn.decl.name.val.clone(),
                    format!("Func_{}", fn_defn.decl.name.val),
                );
            }
            DeclT::FnDecl(fn_decl) => {
                map.insert(
                    fn_decl.name.val.clone(),
                    format!("Func_{}", fn_decl.name.val),
                );
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

/// Tracks whether an emitted expression is an F* lvalue (ref a) or rvalue (a).
enum ExprKind {
    LValue(Doc),
    RValue(Doc),
}

impl ExprKind {
    /// Convert to an rvalue (F* type `a`). Dereferences lvalues with `!`.
    fn to_rvalue(self) -> Doc {
        match self {
            ExprKind::LValue(doc) => parens(Doc::text("!").append(doc)),
            ExprKind::RValue(doc) => doc,
        }
    }

    /// Extract the raw document without rvalue/lvalue conversion.
    fn into_doc(self) -> Doc {
        match self {
            ExprKind::LValue(doc) | ExprKind::RValue(doc) => doc,
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

    StructFieldProj(Rc<IdentT>, Rc<IdentT>),
    StructDirectFieldName(Rc<IdentT>, Rc<IdentT>),
    StructGhostFieldProj(Rc<IdentT>, Rc<IdentT>),
    StructAuxFn(Rc<IdentT>, String),

    UnionFieldConstructor(Rc<IdentT>, Rc<IdentT>),
    UnionGhostFieldProj(Rc<IdentT>, Rc<IdentT>),
    UnionFieldProj(Rc<IdentT>, Rc<IdentT>),
    UnionAuxFn(Rc<IdentT>, &'static str, Rc<IdentT>),

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
            Name::UnionFieldConstructor(u, fld) => {
                format!("Field_{}__{}", u, fld)
            }
            Name::UnionGhostFieldProj(u, fld) => format!("{}__{}", union_to_string(u), fld),
            Name::UnionFieldProj(u, fld) => format!("{}__get_{}", union_to_string(u), fld),
            Name::UnionAuxFn(u, f, fld) => format!("{}__aux_{}_{}", union_to_string(u), f, fld),
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
}

impl<'a> Emitter<'a> {
    fn report(&mut self, msg: String, loc: &SourceInfo) {
        self.diags.report(Diagnostic {
            loc: loc.location().clone(),
            level: DiagnosticLevel::Error,
            msg,
        });
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

                TypeT::Bool => Doc::text("bool"),
                TypeT::SizeT => Doc::text("SizeT.t"),
                TypeT::PtrdiffT => Doc::text("Pulse.Lib.C.PtrdiffT.t"),

                TypeT::Pointer(to, PointerKind::Array | PointerKind::ArrayPtr) => {
                    unaryfn(Doc::text("array"), self.emit_type(env, to))
                }
                TypeT::Pointer(to, PointerKind::Ref | PointerKind::Unknown) => {
                    unaryfn(Doc::text("ref"), self.emit_type(env, to))
                }
                TypeT::Unknown => Doc::text("unit"),
                TypeT::Error => Doc::text("unit"),

                TypeT::TypeRef(n) => self.emit_name(Name::TypeRef(n.into())),

                TypeT::SLProp => Doc::text("slprop"),
                TypeT::SpecInt => Doc::text("int"),
                TypeT::SpecNat => Doc::text("nat"),

                TypeT::Refine(ty, _)
                | TypeT::RefineAlways(ty, _)
                | TypeT::RefineUninit(ty, _)
                | TypeT::RefineValue(ty, ..)
                | TypeT::Plain(ty) => self.emit_type(env, ty),
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
            TypeT::Bool => Doc::text("false"),
            TypeT::SizeT => Doc::text("0sz"),
            TypeT::Pointer(_, PointerKind::Ref | PointerKind::Unknown) => Doc::text("null"),
            TypeT::Pointer(_, PointerKind::Array | PointerKind::ArrayPtr) => {
                Doc::text("zero_default")
            }
            TypeT::Void => Doc::text("()"),
            TypeT::TypeRef(_) => Doc::text("zero_default"),
            TypeT::Refine(ty, _)
            | TypeT::RefineAlways(ty, _)
            | TypeT::RefineUninit(ty, _)
            | TypeT::RefineValue(ty, ..)
            | TypeT::Plain(ty) => self.emit_type_default(env, ty),
            _ => {
                self.report(format!("no zero default for type {}", ty), &ty.loc);
                Doc::text("(admit())")
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
            ExprT::Malloc(_) | ExprT::Calloc(_) => {}
            ExprT::MallocArray(_, count) | ExprT::CallocArray(_, count) => {
                self.subst_this_rvalue(env, Rc::make_mut(count), this);
            }
            ExprT::Free(val) => self.subst_this_rvalue(env, Rc::make_mut(val), this),
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
                            if field_name.is_some() {
                                self.report(
                                    format!("${}: struct type does not take a field name", kind.keyword()),
                                    &ty.loc,
                                );
                            }
                            Doc::text(*before).append(self.emit_name(Name::StructAuxFn(
                                struct_name.val.clone(),
                                kind.struct_aux_name().into(),
                            )))
                        }
                        TypeT::TypeRef(TypeRefKind::Union(union_name)) => {
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
                let raw = Doc::text(self.nm.mangle(&Name::Val(extract_base_ident(this), idx)).to_string());
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
                let spec_field_name = Doc::text(self.nm.mangle(&Name::TypeRefSpecField(
                    (*type_ref).clone(),
                    spec_field_name_str,
                )).to_string());
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
                let spec_field_name = Doc::text(self.nm.mangle(&Name::TypeRefSpecField(
                    (*type_ref).clone(),
                    format!("{}", raw_name.pretty(80)),
                )).to_string());
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
        match &ty.val {
            TypeT::Void
            | TypeT::Bool
            | TypeT::Int { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::SpecInt
            | TypeT::SpecNat
            | TypeT::SLProp
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
                                self.emit_type_slprop(
                                    env, pointee_ty, variant, naming, props, &derefed,
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
                        let val_name = self.push_val_binding(
                            naming,
                            this,
                            unaryfn(Doc::text("full_array_spec"), pointee_type_doc),
                        );
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
                }
            }
            TypeT::TypeRef(n) => {
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
                self.emit_type_slprop(env, ty, variant, naming, props, this);
                if let SLPropVariant::Init { .. } = variant {
                    let p = &mut p.clone();
                    self.subst_this_rvalue(env, Rc::make_mut(p), this);
                    props.push(self.emit_rvalue(env, p));
                }
            }
            TypeT::RefineAlways(ty, p) => {
                self.emit_type_slprop(env, ty, variant, naming, props, this);
                let p = &mut p.clone();
                self.subst_this_rvalue(env, Rc::make_mut(p), this);
                props.push(self.emit_rvalue(env, p));
            }
            TypeT::RefineUninit(ty, p) => {
                self.emit_type_slprop(env, ty, variant, naming, props, this);
                if let SLPropVariant::Uninit = variant {
                    let p = &mut p.clone();
                    self.subst_this_rvalue(env, Rc::make_mut(p), this);
                    props.push(self.emit_rvalue(env, p));
                }
            }
            TypeT::RefineValue(ty, binding_name, binding_ty, p) => {
                self.emit_type_slprop(env, ty, variant, naming, props, this);
                if let SLPropVariant::Init { .. } = variant {
                    let binding_type_doc = self.emit_type(env, binding_ty);
                    // RefineValue uses an explicit binding name from the user annotation
                    let raw_name = Doc::text(binding_name.val.to_string());
                    let val_name =
                        self.push_val_binding_explicit(naming, raw_name, binding_type_doc);
                    let _ = val_name; // name is used implicitly in the refinement prop
                    let p = &mut p.clone();
                    self.subst_this_rvalue(env, Rc::make_mut(p), this);
                    props.push(self.emit_rvalue(env, p));
                }
            }
            TypeT::Plain(_) => {}
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
            ExprKind::RValue(_) => {
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
                // *arrayptr → arrayptr_read at index 0
                let is_arrayptr = env
                    .infer_expr(inner)
                    .map(|ty| {
                        matches!(
                            env.vtype_whnf(ty).val,
                            TypeT::Pointer(_, PointerKind::ArrayPtr)
                        )
                    })
                    .unwrap_or(false);
                if is_arrayptr {
                    let inner_doc = self.emit_rvalue(env, inner);
                    ExprKind::RValue(annotated(v, || {
                        parens(naryfn([
                            Doc::text("arrayptr_read"),
                            inner_doc,
                            Doc::text("0sz"),
                        ]))
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
                            match self.emit_expr(env, x) {
                                ExprKind::LValue(x_doc) => ExprKind::LValue(annotated(v, || {
                                    unaryfn(
                                        self.emit_name(Name::StructFieldProj(
                                            struct_name.val.clone(),
                                            a.val.clone(),
                                        )),
                                        x_doc,
                                    )
                                })),
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
                            match self.emit_expr(env, x) {
                                ExprKind::LValue(x_doc) => ExprKind::LValue(annotated(v, || {
                                    unaryfn(
                                        self.emit_name(Name::UnionFieldProj(
                                            union_name.val.clone(),
                                            a.val.clone(),
                                        )),
                                        x_doc,
                                    )
                                })),
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
                let is_arrayptr = env
                    .infer_expr(arr)
                    .map(|ty| {
                        matches!(
                            env.vtype_whnf(ty).val,
                            TypeT::Pointer(_, PointerKind::ArrayPtr)
                        )
                    })
                    .unwrap_or(false);
                let arr_doc = self.emit_rvalue(env, arr);
                let idx_doc = self.emit_rvalue(env, idx);
                let fn_name = if is_arrayptr {
                    "arrayptr_read"
                } else {
                    "array_read"
                };
                ExprKind::RValue(annotated(v, || {
                    parens(naryfn([Doc::text(fn_name), arr_doc, idx_doc]))
                }))
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
            | TypeT::Plain(ty),
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
            TypeT::Int { .. } | TypeT::SizeT | TypeT::PtrdiffT | TypeT::Pointer(..),
        )
        | (
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr,
            TypeT::Bool | TypeT::SizeT | TypeT::PtrdiffT,
        )
        | (_, TypeT::SLProp)
        | (_, TypeT::Error)
        | (_, TypeT::Unknown) => return None,
    })
}

impl<'a> Emitter<'a> {
    fn emit_rvalue(&mut self, env: &Env, v: &Expr) -> Doc {
        self.emit_expr(env, v).to_rvalue()
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
                            width,
                        } => Doc::text(format!("(Int{}.int_to_t {})", width, val)),
                        TypeT::Int {
                            signed: false,
                            width,
                        } => Doc::text(format!("(UInt{}.uint_to_t {})", width, val)),
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
                        _ => {
                            self.report(
                                format!("unsupported integer literal type for {}", val),
                                &v.loc,
                            );
                            Doc::text(format!("(admit()) (* {} *)", val))
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
                ExprT::Ref(v) => self.emit_lvalue(env, v),
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
                        // (TypeT::Bool, TypeT::SizeT) => todo!(),
                        (TypeT::Bool, TypeT::SLProp) => unaryfn(Doc::text("with_pure"), val_doc),
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
                        // (TypeT::SizeT, TypeT::Bool) => todo!(),
                        // (TypeT::SizeT, TypeT::Int { signed, width }) => todo!(),
                        // (TypeT::SizeT, TypeT::SLProp) => todo!(),
                        // (TypeT::Pointer { to, kind }, TypeT::Bool) => todo!(),
                        (TypeT::Pointer(_, kind), TypeT::Bool) => {
                            let is_null_fn = match kind {
                                PointerKind::Array | PointerKind::ArrayPtr => "array_is_null",
                                _ => "Pulse.Lib.Reference.is_null",
                            };
                            unaryfn(Doc::text("not"), unaryfn(Doc::text(is_null_fn), val_doc))
                        }
                        // (TypeT::Pointer { to, kind }, TypeT::SizeT) => todo!(),
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
                        (TypeT::Pointer(_, _), TypeT::Pointer(_, to_kind)) => {
                            // Pointer kind change (e.g., Ref→ArrayPtr for null)
                            if matches!(&val.val, ExprT::IntLit(n, _) if **n == BigInt::ZERO) {
                                match to_kind {
                                    PointerKind::Ref | PointerKind::Unknown => Doc::text("null"),
                                    PointerKind::Array | PointerKind::ArrayPtr => {
                                        Doc::text("array_null")
                                    }
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
                        unaryfn(
                            Doc::text("Pulse.Lib.C.Array.live_array"),
                            self.emit_lvalue(env, v),
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
                ExprT::StructInit(name, fields) => Doc::text("{")
                    .append(Doc::concat(fields.iter().map(|(fld, val)| {
                        Doc::line()
                            .append(self.emit_name(Name::StructDirectFieldName(
                                name.val.clone(),
                                fld.val.clone(),
                            )))
                            .append("=")
                            .append(self.emit_rvalue(env, val))
                            .append(";")
                    })))
                    .nest(2)
                    .append(Doc::line())
                    .append("}")
                    .group(),
                ExprT::UnionInit(name, fld, val) => unaryfn(
                    self.emit_name(Name::UnionFieldConstructor(
                        name.val.clone(),
                        fld.val.clone(),
                    )),
                    self.emit_rvalue(env, val),
                ),
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
                ExprT::AssignExpr(_, _) => {
                    self.report(
                        "assignment expression should have been lowered".to_string(),
                        &v.loc,
                    );
                    Doc::text("(admit())")
                }
            }
        })
    }

    fn emit_stmt(&mut self, env: &Env, stmt: &Stmt) -> Doc {
        annotated(stmt, || {
            match &stmt.val {
                StmtT::Call(v) => self.emit_rvalue(env, v).append(";").nest(2).group(),
                StmtT::Decl(x, ty) => {
                    let x = self.emit_name(Name::Var(x.val.clone()));
                    (Doc::text("let mut ").append(x).append(" :"))
                        .append(Doc::line())
                        .append(self.emit_type(env, ty))
                        .append(";")
                        .nest(2)
                        .group()
                }
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
                        naryfn([
                            Doc::text(fn_name),
                            self.emit_rvalue(env, arr),
                            self.emit_rvalue(env, idx),
                            self.emit_rvalue(env, t),
                        ])
                        .append(";")
                        .nest(2)
                        .group()
                    } else if let ExprT::Deref(inner) = &x.val {
                        // Check if dereferencing an arrayptr: *p = val → arrayptr_write p 0sz val
                        let is_arrayptr = env
                            .infer_expr(inner)
                            .map(|ty| {
                                matches!(
                                    env.vtype_whnf(ty).val,
                                    TypeT::Pointer(_, PointerKind::ArrayPtr)
                                )
                            })
                            .unwrap_or(false);
                        if is_arrayptr {
                            naryfn([
                                Doc::text("arrayptr_write"),
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
                        // Fall through to normal assignment for struct members
                        self.emit_lvalue(env, x)
                            .append(Doc::line())
                            .append(":=")
                            .group()
                            .append(Doc::line())
                            .append(self.emit_rvalue(env, t))
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
                StmtT::If(c, b1, b2) => Doc::text("if ")
                    .append(parens(self.emit_rvalue(env, c)))
                    .nest(2)
                    .append(" ")
                    .append(self.emit_block(env, b1))
                    .append(" else ")
                    .append(self.emit_block(env, b2))
                    .append(";")
                    .group(),
                StmtT::While {
                    cond,
                    inv,
                    requires,
                    ensures,
                    body,
                } => Doc::text("while ")
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
                    })))
                    .nest(2)
                    .append(self.emit_block(env, body))
                    .append(";")
                    .group(),
                StmtT::Break => Doc::text("break;"),
                StmtT::Continue => Doc::text("continue;"),
                StmtT::Return(Some(t)) => Doc::text("return")
                    .append(Doc::line())
                    .append(self.emit_rvalue(env, t))
                    .append(";")
                    .group()
                    .nest(2),
                StmtT::Return(None) => Doc::text("return;"),
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
        Doc::concat(stmts.iter().map(|stmt| {
            let doc = Doc::line().append(self.emit_stmt(&env, stmt));
            env.push_stmt(stmt);
            doc
        }))
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

impl<'a> Emitter<'a> {
    fn emit_typedef(&mut self, env: &Env, decl @ TypeDefn { name, body }: &TypeDefn) -> Doc {
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
            self.emit_name(Name::Var(this.val.clone()))
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
        let default_decl = Doc::text("instance")
            .append(Doc::line())
            .append(default_name)
            .append(Doc::line())
            .append(":")
            .append(Doc::line())
            .append(unaryfn(Doc::text("has_zero_default"), type_name))
            .append(Doc::line())
            .append("=")
            .append(Doc::line())
            .append("{")
            .group()
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
            .group();

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
                    .append(struct_type_name)
                    .append(Doc::line())
                    .append("->")
                    .append(Doc::line())
                    .append("slprop")
                    .group(),
            ],
            Doc::hardline(),
        )
    }

    fn emit_structdefn(
        &mut self,
        env: &Env,
        decl @ StructDefn { name, fields }: &StructDefn,
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
                .append(Doc::concat(fields.iter().map(|(fld, fld_ty)| {
                    Doc::hardline().append(
                        self.emit_name(direct_fld(fld))
                            .append(":")
                            .append(Doc::line())
                            .append(self.emit_type(env, fld_ty))
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
        let spec_param_name = Doc::text(self.nm.mangle(&Name::Val(name.val.clone(), 0)).to_string());

        // Collect per-field spec info using emit_type_slprop with SpecRecord naming
        let type_ref = TypeRef::from(k);
        let field_specs: Vec<FieldSpecInfo> = fields
            .iter()
            .map(|(fld, fld_ty)| {
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
                    fld_ty,
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
        let spec_type_name = Doc::text(self.nm.mangle(&Name::TypeRefSpec(k.into())).to_string());
        if !all_spec_bindings.is_empty() {
            ses.push(
                Doc::text("[@@erasable] noeq type")
                    .append(Doc::line())
                    .append(spec_type_name.clone())
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
                .insert(TypeRef::from(k), vec![spec_type_name.clone()]);
        }

        // Collect init props from field specs
        let init_props: Vec<Doc> = field_specs
            .iter()
            .flat_map(|fs| fs.init_props.clone())
            .collect();

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
                        .append(spec_type_name.clone()),
                ),
            ];
            ses.push(
                Doc::text("let")
                    .append(Doc::line())
                    .append("predicate")
                    .append(Doc::line())
                    .append(pred_name.clone())
                    .group()
                    .append(
                        Doc::concat(pred_args.iter().map(|arg| Doc::line().append(arg.clone())))
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
        } else {
            // No spec bindings - emit a simple pred with just this and perm
            ses.push(mk_eager_unfold_slprop(
                pred_name.clone(),
                &[this_arg.clone(), parens(Doc::text("p: perm"))],
                Doc::text("emp"),
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
                for (fld, fld_ty) in fields {
                    let field_expr = ExprT::Member(mk_rvar(&this_r), fld.clone().into())
                        .with_loc(fld.loc.clone());
                    s.emit_type_slprop(env, fld_ty, variant, naming, props, &field_expr);
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
        if !all_spec_bindings.is_empty() {
            let unfold_name = Doc::text(self.nm.mangle(&Name::TypeRefPredUnfold(k.into())).to_string());
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
                            .append(spec_type_name.clone())
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
        if !all_spec_bindings.is_empty() {
            let fold_name = Doc::text(self.nm.mangle(&Name::TypeRefPredFold(k.into())).to_string());

            // Build per-binding val params for fold
            let mut fold_val_params: Vec<Doc> = vec![];
            let mut fold_spec_record_fields: Vec<Doc> = vec![];
            for fs in &field_specs {
                for (i, binding) in fs.bindings.iter().enumerate() {
                    let val_name = Doc::text(format!("val_{}_{}", fs.field_ident, i));
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
            for (fld, fld_ty) in fields {
                let field_expr =
                    ExprT::Member(mk_rvar(&this), fld.clone().into()).with_loc(fld.loc.clone());
                let mut field_bindings = vec![];
                let mut naming = ValNaming::Standard {
                    quote: false,
                    bindings: &mut field_bindings,
                };
                self.emit_type_slprop(
                    env,
                    fld_ty,
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

        for (fld, fld_ty) in fields {
            let ll_type = self.emit_type(env, fld_ty);

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
                    .append(unaryfn(Doc::text("ref"), ll_type))
                    .group(),
            ));
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
                    for (fld, _) in fields {
                        post.push(naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            Doc::text("#p"),
                            Doc::text("vx.").append(self.emit_name(direct_fld(fld))),
                        ]));
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
                for (fld, _) in fields {
                    args.push(fold_arg_name(fld))
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
                    for (fld, _) in fields {
                        pre.push(naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            Doc::text("#p"),
                            fold_arg_name(fld),
                        ]));
                    }
                    mk_star(pre)
                },
                mk_thunk(naryfn([
                    Doc::text("Pulse.Lib.Reference.pts_to"),
                    Doc::text("x"),
                    Doc::text("#p"),
                    Doc::text("{")
                        .append(Doc::concat(fields.iter().map(|(fld, _)| {
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
                    for (fld, _) in fields {
                        pre.push(naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                        ]));
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
                    for (fld, _) in fields {
                        post.push(naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to_uninit"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                        ]));
                    }
                    mk_star(post)
                }),
            ]),
        ));

        for (fld, fld_ty) in fields {
            let ll_ty = self.emit_type(env, fld_ty);
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
                    unaryfn(Doc::text("ref"), ll_ty),
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

        // has_zero_default instance
        let default_name = self.emit_name(Name::TypeRefDefault(k.into()));
        ses.push(
            Doc::text("instance")
                .append(Doc::line())
                .append(default_name)
                .append(Doc::line())
                .append(":")
                .append(Doc::line())
                .append(unaryfn(
                    Doc::text("has_zero_default"),
                    struct_type_name.clone(),
                ))
                .append(Doc::line())
                .append("=")
                .append(Doc::line())
                .append("{")
                .group()
                .append(Doc::line())
                .append(Doc::text("zero_default = {"))
                .append(Doc::concat(fields.iter().map(|(fld, fld_ty)| {
                    Doc::line()
                        .append(self.emit_name(direct_fld(fld)))
                        .append(" =")
                        .append(Doc::line())
                        .append(self.emit_type_default(env, fld_ty))
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
        );

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
                .append(Doc::concat(fields.iter().map(|(fld, fld_ty)| {
                    Doc::hardline().append(
                        Doc::text("| ")
                            .append(self.emit_name(field_ctor(fld)))
                            .append(Doc::text(" :"))
                            .append(Doc::line())
                            .append(self.emit_type(env, fld_ty))
                            .append(Doc::text(" ->"))
                            .append(Doc::line())
                            .append(union_type_name.clone())
                            .group()
                            .nest(2),
                    )
                })))
                .group(),
        );

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
        for (fld, _) in fields {
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

        // Emit ghost field projections
        for (fld, fld_ty) in fields {
            let ll_type = self.emit_type(env, fld_ty);
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
                    .append(unaryfn(Doc::text("ref"), ll_type))
                    .group(),
            ));
        }

        // Per-field unfold: requires pts_to x #p vx ** pure (Field_foo__x? vx)
        // gives back unfolded token + pts_to of the field ref
        for (fld, fld_ty) in fields {
            let ll_type = self.emit_type(env, fld_ty);
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
                    mk_thunk(mk_star([
                        naryfn([
                            self.emit_name(unfolded_tok(fld)),
                            Doc::text("x"),
                            Doc::text("p"),
                        ]),
                        naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            Doc::text("#p"),
                            parens(
                                ctor_name
                                    .clone()
                                    .append("?._0")
                                    .append(Doc::line())
                                    .append("vx")
                                    .group(),
                            ),
                        ]),
                    ])),
                ]),
            ));

            // Per-field fold: takes unfolded token + field pts_to, gives back pts_to x (Ctor val)
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
                            .append(ll_type.clone()),
                    ),
                ],
                naryfn([
                    Doc::text("stt_ghost"),
                    Doc::text("unit"),
                    Doc::text("emp_inames"),
                    mk_star([
                        naryfn([
                            self.emit_name(unfolded_tok(fld)),
                            Doc::text("x"),
                            Doc::text("p"),
                        ]),
                        naryfn([
                            Doc::text("Pulse.Lib.Reference.pts_to"),
                            unaryfn(self.emit_name(ghost_fld(fld)), Doc::text("x")),
                            Doc::text("#p"),
                            Doc::text(format!("v_{}", fld)),
                        ]),
                    ]),
                    mk_thunk(naryfn([
                        Doc::text("Pulse.Lib.Reference.pts_to"),
                        Doc::text("x"),
                        Doc::text("#p"),
                        unaryfn(ctor_name.clone(), Doc::text(format!("v_{}", fld))),
                    ])),
                ]),
            ));
        }

        // Field getter functions (stt_atomic, like structs)
        for (fld, fld_ty) in fields {
            let ll_ty = self.emit_type(env, fld_ty);
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
                    unaryfn(Doc::text("ref"), ll_ty),
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

        // has_zero_default instance (uses first field's constructor)
        if let Some((first_fld, first_fld_ty)) = fields.first() {
            let default_name = self.emit_name(Name::TypeRefDefault(k.into()));
            let first_ctor = self.emit_name(Name::UnionFieldConstructor(
                name.val.clone(),
                first_fld.val.clone(),
            ));
            ses.push(
                Doc::text("instance")
                    .append(Doc::line())
                    .append(default_name)
                    .append(Doc::line())
                    .append(":")
                    .append(Doc::line())
                    .append(unaryfn(
                        Doc::text("has_zero_default"),
                        union_type_name.clone(),
                    ))
                    .append(Doc::line())
                    .append("=")
                    .append(Doc::line())
                    .append("{")
                    .group()
                    .append(Doc::line())
                    .append(
                        Doc::text("zero_default =")
                            .append(Doc::line())
                            .append(unaryfn(
                                first_ctor,
                                self.emit_type_default(env, first_fld_ty),
                            ))
                            .group(),
                    )
                    .nest(2)
                    .append(Doc::line())
                    .append("}")
                    .group(),
            );
        }

        Doc::intersperse(ses.into_iter().map(|se| se.group()), Doc::hardline())
    }

    fn emit_fn_sig(
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
            decreases,
        }: &FnDecl,
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

        let fn_keyword = if *is_rec {
            Doc::text("fn rec")
        } else {
            Doc::text("fn")
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
        .append(match decreases {
            Some(dec) => Doc::hardline().append(
                Doc::text("decreases")
                    .append(Doc::line())
                    .append(self.emit_rvalue(env, dec))
                    .nest(2)
                    .group(),
            ),
            None => Doc::nil(),
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

    /// Check that a parameter type is valid for a pure function (no pointers, arrays, etc.)
    fn check_pure_type(&mut self, ty: &Type) {
        match &ty.val {
            TypeT::Void
            | TypeT::Bool
            | TypeT::Int { .. }
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
            TypeT::Refine(inner, _)
            | TypeT::RefineAlways(inner, _)
            | TypeT::RefineUninit(inner, _)
            | TypeT::RefineValue(inner, ..)
            | TypeT::Plain(inner) => self.check_pure_type(inner),
        }
    }

    fn emit_pure_body(&mut self, env: &Env, stmts: &[Rc<Stmt>]) -> Doc {
        if stmts.is_empty() {
            return Doc::text("()");
        }

        match &stmts[0].val {
            StmtT::Return(Some(e)) if stmts.len() == 1 => self.emit_rvalue(env, e),
            StmtT::Return(None) if stmts.len() == 1 => Doc::text("()"),

            StmtT::If(cond, then_body, else_body) => {
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
        if decl.is_rec {
            body
        } else {
            Doc::text("unfold").append(Doc::hardline()).append(body)
        }
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
            ])
        } else {
            ret_type_doc
        };

        let body_doc = if matches!(let_decl.ret_type.val, TypeT::SLProp) {
            self.emit_pure_prop(env, &let_decl.body)
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
        if let_decl.is_rec {
            body
        } else {
            Doc::text("unfold").append(Doc::hardline()).append(body)
        }
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
        match &gv.init {
            Some(init) => {
                let init_doc = self.emit_rvalue(env, init);
                Doc::text("unfold")
                    .append(Doc::hardline())
                    .append(Doc::text("let "))
                    .append(name)
                    .append(" : ")
                    .append(ty)
                    .append(" = ")
                    .append(init_doc)
            }
            None => {
                let default_doc = self.emit_type_default(env, &gv.ty);
                Doc::text("unfold")
                    .append(Doc::hardline())
                    .append(Doc::text("let "))
                    .append(name)
                    .append(" : ")
                    .append(ty)
                    .append(" = ")
                    .append(default_doc)
            }
        }
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
    pub range_map: SourceRangeMap,
}

/// Emit each declaration as its own module.
/// Returns a list of (module_name, code, source_range_map) for each declaration.
pub fn emit_multifile(diags: &mut Diagnostics, tu: &TranslationUnit) -> Vec<EmittedModule> {
    // First pass: build env with all decls (needed for type lookups during emission)
    let mut full_env = Env::new();
    for decl in &tu.decls {
        full_env.push_decl(decl);
    }

    // Also pre-register recursive functions
    let mut rec_env = Env::new();
    for decl in &tu.decls {
        if let DeclT::FnDefn(FnDefn { decl: fn_decl, .. }) = &decl.val {
            if fn_decl.is_rec {
                rec_env.push_fn_decl(fn_decl.clone());
            }
        }
    }

    // Build the map from function/let/global identifiers to their owning modules
    let fn_module_map = build_fn_module_map(&tu.decls);
    // Build the override map for OpaqueTypeDecl typedef names
    let typedef_override_map = build_typedef_override_map(&tu.decls);

    // Collect include module names for open directives
    let include_modules: Vec<String> = tu
        .decls
        .iter()
        .filter_map(|d| {
            if let DeclT::IncludeDecl(inc) = &d.val {
                Some(inc.module_name.to_string())
            } else {
                None
            }
        })
        .collect();
    // Collect let module names for open directives (needed for proof visibility)
    let let_modules: Vec<String> = tu
        .decls
        .iter()
        .filter_map(|d| {
            if let DeclT::LetDecl(ld) = &d.val {
                Some(format!("Let_{}", ld.name.val))
            } else {
                None
            }
        })
        .collect();
    // Collect opaque type module names for open directives
    let type_modules: Vec<String> = tu
        .decls
        .iter()
        .filter_map(|d| {
            if let DeclT::OpaqueTypeDecl(td) = &d.val {
                Some(format!("Type_{}", td.name.val))
            } else {
                None
            }
        })
        .collect();

    let mut results = Vec::new();
    // Use a single NameMangling instance shared across all modules to ensure
    // consistent mangled names for cross-references.
    let mut nm = NameMangling::new();
    // Accumulate type_val_params across modules so that later modules know about
    // val params registered by earlier typedef/struct definitions.
    let mut type_val_params: HashMap<TypeRef, Vec<Doc>> = HashMap::new();
    let mut type_uninit_val_params: HashMap<TypeRef, Vec<Doc>> = HashMap::new();

    // First pass: emit all modules, collecting code bodies (without opens in preamble for non-Func)
    struct PendingModule {
        mod_name: String,
        decl_kind: DeclKind,
        body_code: String,
        range_map: crate::pass::emit::SourceRangeMap,
    }
    #[derive(Clone, Copy, PartialEq)]
    enum DeclKind {
        Func,      // FnDefn, FnDecl, GlobalVar
        StructTU,  // StructDefn, StructDecl, UnionDefn, Typedef
        Auxiliary, // IncludeDecl, LetDecl, OpaqueTypeDecl
    }

    let mut pending: Vec<PendingModule> = Vec::new();

    for decl in &tu.decls {
        let mod_name = module_name_for_decl(decl);

        // Build env for this decl: include all prior decls + rec fns
        let mut env = rec_env.clone();
        for d in &tu.decls {
            if std::ptr::eq(d, decl) {
                break;
            }
            env.push_decl(d);
        }

        let emitter = &mut Emitter {
            nm: nm.clone(),
            diags,
            type_val_params: type_val_params.clone(),
            type_uninit_val_params: type_uninit_val_params.clone(),
            defining_struct: None,
            current_module: mod_name.clone(),
            fn_module_map: fn_module_map.clone(),
            typedef_override_map: typedef_override_map.clone(),
        };

        // Emit just the body (decl code)
        let body_doc = emitter.emit_decl(&env, decl);
        let body_with_restart = Doc::text("#restart-solver")
            .append(Doc::hardline())
            .append(Doc::hardline())
            .append(body_doc);
        let mut writer = StrWriter::new();
        body_with_restart.render_raw(100, &mut writer).unwrap();

        // Merge back the name mangling state so subsequent modules see the same mappings
        nm = emitter.nm.clone();
        // Merge back type_val_params so later modules can see val params from earlier typedefs/structs
        for (k, v) in &emitter.type_val_params {
            type_val_params
                .entry(k.clone())
                .or_insert_with(|| v.clone());
        }
        for (k, v) in &emitter.type_uninit_val_params {
            type_uninit_val_params
                .entry(k.clone())
                .or_insert_with(|| v.clone());
        }

        let decl_kind = match &decl.val {
            DeclT::FnDefn(_) | DeclT::FnDecl(_) | DeclT::GlobalVar(_) => DeclKind::Func,
            DeclT::StructDefn(_)
            | DeclT::StructDecl(_)
            | DeclT::UnionDefn(_)
            | DeclT::Typedef(_) => DeclKind::StructTU,
            _ => DeclKind::Auxiliary,
        };

        pending.push(PendingModule {
            mod_name,
            decl_kind,
            body_code: writer.buffer,
            range_map: writer.source_range_map,
        });
    }

    // Build dependency sets for each module based on direct body text references.
    use std::collections::HashSet;
    let all_module_names: Vec<String> = pending.iter().map(|pm| pm.mod_name.clone()).collect();

    // Build a map of symbols defined in each auxiliary module.
    // We detect definitions by looking for common F* declaration patterns in the emitted code.
    let mut symbol_to_module: HashMap<String, String> = HashMap::new();
    for pm in &pending {
        if pm.decl_kind == DeclKind::Auxiliary {
            // Extract defined names: look for patterns like "let name", "fn name", "ghost fn name", "val name"
            for line in pm.body_code.lines() {
                let trimmed = line.trim();
                // Match "let <name>", "let rec <name>", "fn <name>", "ghost fn <name>", "val <name>"
                let words: Vec<&str> = trimmed.split_whitespace().collect();
                let name = if words.len() >= 2
                    && (words[0] == "let" || words[0] == "fn" || words[0] == "val")
                {
                    // skip "let rec" -> take word after "rec"
                    if words[0] == "let" && words.len() >= 3 && words[1] == "rec" {
                        Some(words[2])
                    } else {
                        Some(words[1])
                    }
                } else if words.len() >= 3 && words[0] == "ghost" && words[1] == "fn" {
                    Some(words[2])
                } else {
                    None
                };
                if let Some(name) = name {
                    // Clean up: remove trailing punctuation
                    let clean_name =
                        name.trim_end_matches(|c: char| !c.is_alphanumeric() && c != '_');
                    if !clean_name.is_empty() && clean_name != "predicate" {
                        symbol_to_module.insert(clean_name.to_string(), pm.mod_name.clone());
                    }
                }
            }
        }
    }

    // Direct references: scan each module's body for occurrences of other module names
    // AND for unqualified uses of symbols defined in auxiliary modules
    let mut direct_refs: HashMap<String, HashSet<String>> = HashMap::new();
    for pm in &pending {
        let mut refs = HashSet::new();
        for other_mod in &all_module_names {
            if *other_mod != pm.mod_name && pm.body_code.contains(other_mod.as_str()) {
                refs.insert(other_mod.clone());
            }
        }
        // Also check for unqualified references to auxiliary-defined symbols
        for (symbol, defining_mod) in &symbol_to_module {
            if *defining_mod != pm.mod_name && pm.body_code.contains(symbol.as_str()) {
                // Verify it's not already qualified (i.e., not preceded by "ModName.")
                let qualified = format!("{}.{}", defining_mod, symbol);
                if !pm.body_code.contains(&qualified) {
                    refs.insert(defining_mod.clone());
                }
            }
        }
        direct_refs.insert(pm.mod_name.clone(), refs);
    }

    // Compute transitive closure of direct_refs (what each module transitively depends on via body text)
    let mut transitive_deps: HashMap<String, HashSet<String>> = direct_refs.clone();
    loop {
        let mut changed = false;
        for mod_name in &all_module_names {
            let current_deps: Vec<String> = transitive_deps
                .get(mod_name)
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default();
            for dep in current_deps {
                let dep_deps: Vec<String> = transitive_deps
                    .get(&dep)
                    .map(|s| s.iter().cloned().collect())
                    .unwrap_or_default();
                for dd in dep_deps {
                    if dd != *mod_name {
                        if transitive_deps
                            .entry(mod_name.clone())
                            .or_default()
                            .insert(dd)
                        {
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Second pass: build final code with appropriate preambles
    for pm in pending {
        let mut preamble = format!("module {}\nopen Pulse\nopen Pulse.Lib.C", pm.mod_name);

        let aux_modules = include_modules
            .iter()
            .chain(let_modules.iter())
            .chain(type_modules.iter());

        match pm.decl_kind {
            DeclKind::Func => {
                // Func/Global modules get all include/let/type opens (safe: nothing depends on Func_*)
                for m in aux_modules {
                    if *m != pm.mod_name {
                        preamble.push_str(&format!("\nopen {}", m));
                    }
                }
            }
            DeclKind::StructTU => {
                // Struct/Typedef/Union: only open modules directly referenced in body
                // AND that don't transitively depend on us
                let my_direct_refs = direct_refs.get(&pm.mod_name).cloned().unwrap_or_default();
                for m in aux_modules {
                    if *m == pm.mod_name {
                        continue;
                    }
                    // Only open if our body actually references this module
                    if !my_direct_refs.contains(m) {
                        continue;
                    }
                    // Check if it transitively depends on us (would create a cycle)
                    let creates_cycle = transitive_deps
                        .get(m)
                        .map_or(false, |deps| deps.contains(&pm.mod_name));
                    if !creates_cycle {
                        preamble.push_str(&format!("\nopen {}", m));
                    }
                }
            }
            DeclKind::Auxiliary => {
                // Auxiliary modules only open other auxiliary modules they directly reference
                let my_direct_refs = direct_refs.get(&pm.mod_name).cloned().unwrap_or_default();
                for m in aux_modules {
                    if *m == pm.mod_name {
                        continue;
                    }
                    // Only open if our body actually references this module
                    if !my_direct_refs.contains(m) {
                        continue;
                    }
                    let creates_cycle = transitive_deps
                        .get(m)
                        .map_or(false, |deps| deps.contains(&pm.mod_name));
                    if !creates_cycle {
                        preamble.push_str(&format!("\nopen {}", m));
                    }
                }
            }
        }

        preamble.push_str("\n#lang-pulse\n\n");
        let full_code = format!("{}{}", preamble, pm.body_code);

        results.push(EmittedModule {
            module_name: pm.mod_name,
            code: full_code,
            range_map: pm.range_map,
        });
    }

    results
}
