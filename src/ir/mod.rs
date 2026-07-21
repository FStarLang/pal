use num_bigint::BigInt;
use std::fmt::{Debug, Display};
use std::rc::Rc;
pub mod pretty;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

impl Range {
    pub fn union(&self, other: &Range) -> Range {
        Range {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl Display for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}:{}-{}:{}",
            self.start.line, self.start.character, self.end.line, self.end.character
        )
    }
}

impl Debug for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Location {
    pub file_name: Rc<str>,
    pub range: Range,
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{:#?}", self.file_name, self.range)
    }
}

impl Debug for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum SourceInfo {
    Original(Location),
    Fallback(Location),
}

impl SourceInfo {
    pub fn location(&self) -> &Location {
        match self {
            SourceInfo::Original(location) => location,
            SourceInfo::Fallback(location) => location,
        }
    }
}

impl Debug for SourceInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Original(loc) => write!(f, "Original({:#?})", loc),
            Self::Fallback(loc) => write!(f, "Fallback({:#?})", loc),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Ast<T> {
    pub val: T,
    pub loc: Rc<SourceInfo>,
}

impl<T> Ast<T> {
    pub fn reuse_loc<S>(&self, val: S) -> Ast<S> {
        Ast {
            loc: self.loc.clone(),
            val,
        }
    }
}

pub trait WithLoc: Sized {
    fn with_loc(self, loc: Rc<SourceInfo>) -> Rc<Ast<Self>> {
        Rc::new(self.with_loc_core(loc))
    }
    fn with_loc_core(self, loc: Rc<SourceInfo>) -> Ast<Self>;
}

impl<T> WithLoc for T {
    #[inline]
    fn with_loc_core(self, loc: Rc<SourceInfo>) -> Ast<Self> {
        Ast { val: self, loc }
    }
}

impl<T: Debug> Debug for Ast<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:#?} @ {:#?}", self.val, self.loc)
    }
}

impl<T: Display> Display for Ast<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.val.fmt(f)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PointerKind {
    Unknown,
    Ref,
    Array,
    ArrayPtr,
    /// An axiomatized, non-parametric raw pointer (`core_ref`). Used to break
    /// type/predicate cycles in (mutually) recursive structs: the pointee type
    /// is retained in the IR for documentation but is dropped on emission, and
    /// no automatic ownership predicate is generated. Introduced by `_core_ref`.
    Core,
}

pub type Type = Ast<TypeT>;
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum TypeT {
    Void,
    Bool,
    Int {
        signed: bool,
        width: u32,
    },
    Float {
        width: u32,
    },
    SizeT,
    PtrdiffT,
    Pointer(Rc<Type>, PointerKind),
    /// Fixed-size C array type `T[N]`. Decays to `Pointer(T, Array)` in
    /// function parameters (handled by the decay pass).
    FixedArray(Rc<Type>, u64),
    /// Flexible (unsized) array member `T[]` appearing as the last field of a
    /// struct. Modeled inline as a ghost `array_spec T` in the struct's noeq
    /// record with no static length pin. An optional length refinement (e.g.
    /// relating it to a sibling `len` field) is attached via `_refines`, which
    /// wraps this in `RefineAlways`; emit lifts that relation into a `pure`
    /// fact in the struct predicate.
    FlexArray(Rc<Type>),

    SpecInt,
    SpecNat,
    SLProp,

    TypeRef(TypeRefKind),

    Refine(Rc<Type>, Rc<Expr>),
    RefineAlways(Rc<Type>, Rc<Expr>),
    /// Refinement that only applies to the uninit variant.
    RefineUninit(Rc<Type>, Rc<Expr>),
    /// Custom existential binding + predicate (init variant only).
    /// RefineValue(inner_type, binding_name, binding_type, predicate)
    RefineValue(Rc<Type>, Rc<Ident>, Rc<Type>, Rc<Expr>),
    Plain(Rc<Type>),

    /// Nullable pointer wrapper. Transparent to the F* type (emits the inner
    /// type unchanged), but the generated separation-logic prop is wrapped in
    /// `unless_null this (…)` so the resource is `emp` when the pointer is null.
    Nullable(Rc<Type>),

    /// Placeholder for type inference (resolved during elaboration).
    Unknown,
    Error,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum TypeRefKind {
    Typedef(Rc<Ident>),
    Struct(Rc<Ident>),
    Union(Rc<Ident>),
}

impl TypeRefKind {
    // Equality ignoring positions
    pub fn alpha_eq(&self, b: &Self) -> bool {
        match (self, b) {
            (TypeRefKind::Typedef(a), TypeRefKind::Typedef(b))
            | (TypeRefKind::Struct(a), TypeRefKind::Struct(b))
            | (TypeRefKind::Union(a), TypeRefKind::Union(b)) => a.val == b.val,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnOp {
    Not,
    Neg,
    BitNot,
}

impl UnOp {
    pub fn to_str(self) -> &'static str {
        match self {
            UnOp::Not => "!",
            UnOp::Neg => "-",
            UnOp::BitNot => "~",
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.to_str())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum BinOp {
    Eq,
    LEq,
    Lt,
    LogAnd,
    LogOr,
    Implies,
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

impl BinOp {
    pub fn to_str(self) -> &'static str {
        match self {
            BinOp::Eq => "==",
            BinOp::LEq => "<=",
            BinOp::Lt => "<",
            BinOp::LogAnd => "&&",
            BinOp::LogOr => "||",
            BinOp::Implies => "==>",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.to_str())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum VAttr {
    /// `array._length` — length of an array
    Length,
    /// `union.field._active` — whether the named field is active
    Active(Rc<Ident>),
}

pub type Expr = Ast<ExprT>;
pub type Exprs = Vec<Rc<Expr>>;
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum ExprT {
    // LValue variants
    Var(Rc<Ident>),
    Deref(Rc<Expr>),
    Member(Rc<Expr>, Rc<Ident>),
    Index(Rc<Expr>, Rc<Expr>),

    // Virtual attribute (introduced by elab)
    VAttr(VAttr, Rc<Expr>),

    // RValue variants
    BoolLit(bool),
    IntLit(Rc<BigInt>, Rc<Type>),
    FloatLit(Rc<str>, Rc<Type>),
    Ref(Rc<Expr>),
    UnOp(UnOp, Rc<Expr>),
    BinOp(BinOp, Rc<Expr>, Rc<Expr>),
    FnCall(Rc<Ident>, Exprs),
    Cast(Rc<Expr>, Rc<Type>),
    /// `_container_of(ptr, struct T, field)` — recover a `ref` to the enclosing
    /// struct `T` from a `ref` to its `field` (the CONTAINING_RECORD / offsetof
    /// idiom). Holds the field pointer, the enclosing struct type, and the field
    /// name. Emitted as the generated `struct_T__field_container ptr`.
    ContainerOf(Rc<Expr>, Rc<Type>, Rc<Ident>),
    InlinePulse(Rc<InlinePulseCode>, Rc<Type>),
    Live(Rc<Expr>),
    Old(Rc<Expr>),
    Forall(Rc<Ident>, Rc<Type>, Rc<Expr>),
    Exists(Rc<Ident>, Rc<Type>, Rc<Expr>),
    StructInit(Rc<Ident>, Vec<(Rc<Ident>, Rc<Expr>)>),
    UnionInit(Rc<Ident>, Rc<Ident>, Rc<Expr>),
    /// Array initializer: element type + list of element values.
    /// Emitted as nested `array_spec_upd` on an `array_spec_zeroed` base.
    ArrayInit(Rc<Type>, Vec<Rc<Expr>>),
    Malloc(Rc<Type>),
    MallocArray(Rc<Type>, Rc<Expr>),
    Calloc(Rc<Type>),
    CallocArray(Rc<Type>, Rc<Expr>),
    /// Flexible-array-member allocation `malloc(sizeof(struct S) + n*sizeof(E))`:
    /// the struct type `S` and the trailing array length `n`. Unlike `Malloc`,
    /// this threads `n` so the emitted allocator yields a struct whose flexible
    /// tail has length `n`. Emitted as the per-struct `struct_S__aux_malloc_flex`.
    MallocFlex(Rc<Type>, Rc<Expr>),
    /// Zeroing counterpart of `MallocFlex` for
    /// `calloc(1, sizeof(struct S) + n*sizeof(E))`. Emitted as
    /// `struct_S__aux_calloc_flex`; the flexible tail comes back zeroed.
    CallocFlex(Rc<Type>, Rc<Expr>),
    /// `memset(ptr, value, sizeof(T) * count)` — element type, destination
    /// pointer, fill value, and element count. Emitted as
    /// `Pulse.Lib.C.Array.memset`.
    Memset(Rc<Type>, Rc<Expr>, Rc<Expr>, Rc<Expr>),
    /// `memset(ptr, 0, sizeof(T))` — zeroing a single object of type `T`
    /// (struct, scalar, etc.) through `ptr`. Only the zero value is supported,
    /// for any type with a `has_zero_default` instance. Emitted as a whole
    /// object write `(*ptr) := zero_default`.
    MemsetZero(Rc<Type>, Rc<Expr>),
    Free(Rc<Expr>),
    PreIncr(Rc<Expr>),
    PostIncr(Rc<Expr>),
    PreDecr(Rc<Expr>),
    PostDecr(Rc<Expr>),
    Cond(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    /// Assignment expression: assigns rhs to lhs, evaluates to rhs.
    /// Lowered to Assign statement + value in elab pass.
    AssignExpr(Rc<Expr>, Rc<Expr>),
    /// `sizeof(T)` — translated to an opaque `c_sizeof T` call where `T`
    /// is the F* type PAL uses to represent the C type being measured.
    SizeOf(Rc<Type>),
    /// `_Alignof(T)` / `__alignof__(T)` — translated to `c_alignof T`.
    AlignOf(Rc<Type>),
    Error(Rc<Type>),
}

pub type IdentT = str;
pub type Ident = Ast<Rc<IdentT>>;

pub type Stmt = Ast<StmtT>;
pub type Stmts = Vec<Rc<Stmt>>;
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum StmtT {
    Call(Rc<Expr>),
    Decl(Rc<Ident>, Rc<Type>),
    DeclStackArray {
        name: Rc<Ident>,
        elem_type: Rc<Type>,
        size: Rc<Expr>,
    },
    Assign(Rc<Expr>, Rc<Expr>),
    If {
        cond: Rc<Expr>,
        then_branch: Rc<Stmts>,
        else_branch: Rc<Stmts>,
        ensures: Rc<Exprs>,
    },
    While {
        cond: Rc<Expr>,
        inv: Rc<Exprs>,
        requires: Rc<Exprs>,
        ensures: Rc<Exprs>,
        body: Rc<Stmts>,
    },
    Break,
    Continue,
    Return(Option<Rc<Expr>>),
    Assert(Rc<Expr>),
    GhostStmt(Rc<InlinePulseCode>),
    Goto(Rc<Ident>),
    Label {
        name: Rc<Ident>,
        ensures: Rc<Exprs>,
    },
    GotoBlock {
        body: Rc<Stmts>,
        label: Rc<Ident>,
        ensures: Rc<Exprs>,
    },
    Error,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct StructDefn {
    pub name: Rc<Ident>,
    pub fields: Vec<Field>,
    pub eager_unfold_pred: bool,
}

impl StructDefn {
    pub fn get_field(&self, name: &Ident) -> Option<Rc<Type>> {
        self.fields
            .iter()
            .find(|f| f.val.name().val == name.val)
            .map(|f| f.val.logical_type(&f.loc))
    }

    /// Whether this struct has a flexible array member (a trailing unsized
    /// array). Such a struct cannot be soundly copied by a whole-object
    /// assignment: in C the flexible array contents are not copied.
    pub fn has_flex_array_member(&self) -> bool {
        self.fields
            .iter()
            .any(|f| f.val.flex_array_info().is_some())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct UnionDefn {
    pub name: Rc<Ident>,
    pub fields: Vec<Field>,
}

impl UnionDefn {
    pub fn get_field(&self, name: &Ident) -> Option<Rc<Type>> {
        self.fields
            .iter()
            .find(|f| f.val.name().val == name.val)
            .map(|f| f.val.logical_type(&f.loc))
    }
}

pub type Field = Ast<FieldT>;
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum FieldT {
    /// A regular field: `T name;`
    /// For fixed-size C array fields (`T name[length]`), the type is `FixedArray(T, length)`.
    Plain { name: Ident, ty: Rc<Type> },
    /// An unsigned bit-field: `T name : width;`. `ty` is the declared underlying
    /// integer type (e.g. `unsigned int`); `width` is the number of bits. The
    /// value is stored directly in the struct record as a range-refined machine
    /// value `(v:UIntW.t{UIntW.v v < pow2 width})` and is not separately
    /// addressable (no extra `ref`/`pts_to` beyond the usual scalar cell).
    BitField {
        name: Ident,
        ty: Rc<Type>,
        width: u32,
    },
}

/// Strip refinement / plain / nullable wrappers from a type to reveal the
/// underlying structural type (e.g. to detect an array field regardless of an
/// enclosing `_refines` / `_plain` annotation).
pub fn peel_type(ty: &Rc<Type>) -> &Rc<Type> {
    match &ty.val {
        TypeT::Refine(inner, _)
        | TypeT::RefineAlways(inner, _)
        | TypeT::RefineUninit(inner, _)
        | TypeT::RefineValue(inner, ..)
        | TypeT::Plain(inner)
        | TypeT::Nullable(inner) => peel_type(inner),
        _ => ty,
    }
}

impl FieldT {
    pub fn name(&self) -> &Ident {
        match self {
            FieldT::Plain { name, .. } => name,
            FieldT::BitField { name, .. } => name,
        }
    }
    pub fn is_array(&self) -> bool {
        match self {
            FieldT::Plain { ty, .. } => {
                matches!(
                    peel_type(ty).val,
                    TypeT::FixedArray(_, _) | TypeT::FlexArray(_)
                )
            }
            FieldT::BitField { .. } => false,
        }
    }

    /// For a bit-field, the number of bits in its declared width; `None` for a
    /// plain field. Doubles as a "this is a bit-field" predicate.
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            FieldT::BitField { width, .. } => Some(*width),
            FieldT::Plain { .. } => None,
        }
    }

    /// For array fields, return the element type and length.
    pub fn fixed_array_info(&self) -> Option<(&Rc<Type>, u64)> {
        match self {
            FieldT::Plain { ty, .. } => match &peel_type(ty).val {
                TypeT::FixedArray(elem_ty, length) => Some((elem_ty, *length)),
                _ => None,
            },
            FieldT::BitField { .. } => None,
        }
    }

    /// For a flexible array member field, return the element type and the
    /// optional length refinement predicate supplied via `_refines`.
    pub fn flex_array_info(&self) -> Option<(&Rc<Type>, Option<&Rc<Expr>>)> {
        let FieldT::Plain { ty, .. } = self else {
            return None;
        };
        let refine = match &ty.val {
            TypeT::RefineAlways(_, p) => Some(p),
            _ => None,
        };
        match &peel_type(ty).val {
            TypeT::FlexArray(elem_ty) => Some((elem_ty, refine)),
            _ => None,
        }
    }

    /// Returns the "logical" type of the field. For a bit-field this is the
    /// declared underlying integer type (e.g. `unsigned int`), which is what a
    /// member access evaluates to before integer promotion.
    pub fn logical_type(&self, _loc: &Rc<SourceInfo>) -> Rc<Type> {
        match self {
            FieldT::Plain { ty, .. } => ty.clone(),
            FieldT::BitField { ty, .. } => ty.clone(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum ParamMode {
    Regular,
    Consumed,
    Const,
    Out,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FnArg {
    pub name: Option<Rc<Ident>>,
    pub ty: Rc<Type>,
    pub mode: ParamMode,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct GhostArg {
    pub name: Rc<Ident>,
    pub ty: Rc<Type>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FnDecl {
    pub name: Rc<Ident>,
    pub ret_type: Rc<Type>,
    pub args: Vec<FnArg>,
    pub ghost_args: Vec<GhostArg>,
    pub requires: Exprs,
    pub ensures: Exprs,
    pub is_pure: bool,
    pub is_rec: bool,
    pub decreases: Option<Rc<Expr>>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FnDefn {
    pub decl: FnDecl,
    pub body: Stmts,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeDefn {
    pub name: Rc<Ident>,
    pub body: Rc<Type>,
    pub is_pointer_view: bool,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct CodeToken {
    pub before: &'static str,
    pub text: Ast<Rc<str>>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct InlineCode {
    pub tokens: Vec<CodeToken>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum AuxFnKind {
    Unfold,
    UnfoldUninit,
    Fold,
    FoldUninit,
    /// `$activate(union U::arm)` — activates a union arm, leaving its payload
    /// uninitialized. Union-only; has no struct form. Emits the per-arm
    /// activation fn `union_<U>__activate_<arm>`.
    Activate,
}

impl AuxFnKind {
    pub fn keyword(self) -> &'static str {
        match self {
            AuxFnKind::Unfold => "unfold",
            AuxFnKind::UnfoldUninit => "unfold-uninit",
            AuxFnKind::Fold => "fold",
            AuxFnKind::FoldUninit => "fold-uninit",
            AuxFnKind::Activate => "activate",
        }
    }

    /// The struct-level aux fn infix, if this kind has a struct form.
    /// `Activate` is union-only and has none.
    pub fn struct_aux_name(self) -> Option<&'static str> {
        match self {
            AuxFnKind::Unfold => Some("raw_unfold"),
            AuxFnKind::UnfoldUninit => Some("raw_unfold_uninit"),
            AuxFnKind::Fold => Some("raw_fold"),
            AuxFnKind::FoldUninit => Some("raw_fold_uninit"),
            AuxFnKind::Activate => None,
        }
    }

    pub fn union_aux_name(self) -> Option<&'static str> {
        match self {
            AuxFnKind::Unfold => Some("raw_unfold"),
            AuxFnKind::Fold => Some("raw_fold"),
            AuxFnKind::UnfoldUninit | AuxFnKind::FoldUninit | AuxFnKind::Activate => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum InlinePulseToken {
    Verbatim(CodeToken),
    RValueAntiquot {
        before: &'static str,
        expr: Rc<Expr>,
    },
    LValueAntiquot {
        before: &'static str,
        expr: Rc<Expr>,
    },
    TypeAntiquot {
        before: &'static str,
        ty: Rc<Type>,
    },
    FieldAntiquot {
        before: &'static str,
        ty: Rc<Type>,
        field_name: Rc<Ident>,
    },
    AuxFnAntiquot {
        before: &'static str,
        ty: Rc<Type>,
        field_name: Option<Rc<Ident>>,
        kind: AuxFnKind,
    },
    Declare {
        ident: Rc<Ident>,
        ty: Rc<Type>,
    },
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct InlinePulseCode {
    pub tokens: Vec<InlinePulseToken>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct IncludeDecl {
    pub module_name: Rc<str>,
    pub code: InlinePulseCode,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct LetDecl {
    pub name: Rc<Ident>,
    pub is_rec: bool,
    pub is_impure: bool,
    pub ret_type: Rc<Type>,
    pub params: Vec<FnArg>,
    pub requires: Exprs,
    pub ensures: Exprs,
    pub body: Rc<Expr>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct OpaqueTypeDecl {
    pub name: Rc<Ident>,
    pub code: InlinePulseCode,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct GlobalVar {
    pub name: Rc<Ident>,
    pub ty: Rc<Type>,
    pub init: Option<Rc<Expr>>,
    pub is_pure: bool,
    pub opaque_to_smt: bool,
}

pub type Decl = Ast<DeclT>;
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum DeclT {
    FnDefn(FnDefn),
    FnDecl(FnDecl),
    Typedef(TypeDefn),
    StructDefn(StructDefn),
    StructDecl(Rc<Ident>),
    UnionDefn(UnionDefn),
    IncludeDecl(IncludeDecl),
    LetDecl(LetDecl),
    OpaqueTypeDecl(OpaqueTypeDecl),
    GlobalVar(GlobalVar),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TranslationUnit {
    pub main_file_names: Vec<Rc<str>>,
    pub decls: Vec<Decl>,
}
