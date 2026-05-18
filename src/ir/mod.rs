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
    SizeT,
    PtrdiffT,
    Pointer(Rc<Type>, PointerKind),

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
    Ref(Rc<Expr>),
    UnOp(UnOp, Rc<Expr>),
    BinOp(BinOp, Rc<Expr>, Rc<Expr>),
    FnCall(Rc<Ident>, Exprs),
    Cast(Rc<Expr>, Rc<Type>),
    InlinePulse(Rc<InlinePulseCode>, Rc<Type>),
    Live(Rc<Expr>),
    Old(Rc<Expr>),
    Forall(Rc<Ident>, Rc<Type>, Rc<Expr>),
    Exists(Rc<Ident>, Rc<Type>, Rc<Expr>),
    StructInit(Rc<Ident>, Vec<(Rc<Ident>, Rc<Expr>)>),
    UnionInit(Rc<Ident>, Rc<Ident>, Rc<Expr>),
    Malloc(Rc<Type>),
    MallocArray(Rc<Type>, Rc<Expr>),
    Calloc(Rc<Type>),
    CallocArray(Rc<Type>, Rc<Expr>),
    Free(Rc<Expr>),
    PreIncr(Rc<Expr>),
    PostIncr(Rc<Expr>),
    PreDecr(Rc<Expr>),
    PostDecr(Rc<Expr>),
    Cond(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    /// Assignment expression: assigns rhs to lhs, evaluates to rhs.
    /// Lowered to Assign statement + value in elab pass.
    AssignExpr(Rc<Expr>, Rc<Expr>),
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
    If(Rc<Expr>, Rc<Stmts>, Rc<Stmts>),
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
    pub fields: Vec<(Ident, Rc<Type>)>,
}

impl StructDefn {
    pub fn get_field(&self, name: &Ident) -> Option<&Rc<Type>> {
        self.fields
            .iter()
            .find(|(field_name, _)| name.val == field_name.val)
            .map(|(_, ty)| ty)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct UnionDefn {
    pub name: Rc<Ident>,
    pub fields: Vec<(Ident, Rc<Type>)>,
}

impl UnionDefn {
    pub fn get_field(&self, name: &Ident) -> Option<&Rc<Type>> {
        self.fields
            .iter()
            .find(|(field_name, _)| name.val == field_name.val)
            .map(|(_, ty)| ty)
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
}

impl AuxFnKind {
    pub fn keyword(self) -> &'static str {
        match self {
            AuxFnKind::Unfold => "unfold",
            AuxFnKind::UnfoldUninit => "unfold-uninit",
            AuxFnKind::Fold => "fold",
            AuxFnKind::FoldUninit => "fold-uninit",
        }
    }

    pub fn struct_aux_name(self) -> &'static str {
        match self {
            AuxFnKind::Unfold => "raw_unfold",
            AuxFnKind::UnfoldUninit => "raw_unfold_uninit",
            AuxFnKind::Fold => "raw_fold",
            AuxFnKind::FoldUninit => "raw_fold_uninit",
        }
    }

    pub fn union_aux_name(self) -> Option<&'static str> {
        match self {
            AuxFnKind::Unfold => Some("raw_unfold"),
            AuxFnKind::Fold => Some("raw_fold"),
            AuxFnKind::UnfoldUninit | AuxFnKind::FoldUninit => None,
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
