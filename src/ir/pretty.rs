use crate::ir::*;
use ::pretty::RcDoc;

fn inline_pulse_code_to_doc<'a>(code: &'a InlinePulseCode) -> RcDoc<'a, ()> {
    RcDoc::concat(code.tokens.iter().map(|tok| {
        match tok {
            InlinePulseToken::Verbatim(ct) => {
                RcDoc::text(ct.before).append(RcDoc::text(ct.text.val.to_string()))
            }
            InlinePulseToken::RValueAntiquot { before, expr } => RcDoc::text(*before)
                .append("$(")
                .append(expr.to_doc())
                .append(")"),
            InlinePulseToken::LValueAntiquot { before, expr } => RcDoc::text(*before)
                .append("$&(")
                .append(expr.to_doc())
                .append(")"),
            InlinePulseToken::TypeAntiquot { before, ty } => RcDoc::text(*before)
                .append("$type(")
                .append(ty.to_doc())
                .append(")"),
            InlinePulseToken::FieldAntiquot {
                before,
                ty,
                field_name,
            } => RcDoc::text(*before)
                .append("$field(")
                .append(ty.to_doc())
                .append("::")
                .append(field_name.to_doc())
                .append(")"),
            InlinePulseToken::AuxFnAntiquot {
                before,
                ty,
                field_name,
                kind,
            } => {
                let doc = RcDoc::text(*before)
                    .append(format!("${}", kind.keyword()))
                    .append("(")
                    .append(ty.to_doc());
                let doc = if let Some(f) = field_name {
                    doc.append("::").append(f.to_doc())
                } else {
                    doc
                };
                doc.append(")")
            }
            InlinePulseToken::Declare { ident, ty } => RcDoc::text("$declare(")
                .append(ty.to_doc())
                .append(" ")
                .append(ident.to_doc())
                .append(")"),
        }
    }))
}

#[macro_export]
macro_rules! impl_display_using_prettyir {
    ($t:ty) => {
        impl ::std::fmt::Display for $t {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}", self.to_doc().pretty(80))
            }
        }
    };
}

pub trait PrettyIR {
    fn to_doc(&self) -> RcDoc<'_, ()>;
}

impl<A: PrettyIR> PrettyIR for Ast<A> {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        self.val.to_doc()
    }
}

impl<A: PrettyIR + ?Sized> PrettyIR for Rc<A> {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        A::to_doc(self)
    }
}

impl<'a, A: PrettyIR> PrettyIR for &'a A {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        A::to_doc(self)
    }
}

impl PrettyIR for str {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::text(self)
    }
}

impl_display_using_prettyir!(TypeRefKind);

impl PrettyIR for TypeRefKind {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            TypeRefKind::Typedef(n) => n.to_doc(),
            TypeRefKind::Struct(n) => RcDoc::text("struct")
                .append(RcDoc::line())
                .append(n.to_doc())
                .group()
                .nest(2),
            TypeRefKind::Union(n) => RcDoc::text("union")
                .append(RcDoc::line())
                .append(n.to_doc())
                .group()
                .nest(2),
        }
    }
}

impl_display_using_prettyir!(TypeT);

impl PrettyIR for TypeT {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            TypeT::Void => RcDoc::text("void"),
            TypeT::Bool => RcDoc::text("_Bool"),
            TypeT::Int { signed, width } => RcDoc::text(if *signed {
                format!("int{}_t", width)
            } else {
                format!("uint{}_t", width)
            }),
            TypeT::SizeT => RcDoc::text("size_t"),
            TypeT::PtrdiffT => RcDoc::text("ptrdiff_t"),
            TypeT::Pointer(ty, PointerKind::Ref) => ty.to_doc().append("*"),
            TypeT::Pointer(ty, PointerKind::Array) => ty.to_doc().append(RcDoc::text("[]")),
            TypeT::Pointer(ty, PointerKind::ArrayPtr) => ty.to_doc().append(RcDoc::text("[ptr]")),
            TypeT::Pointer(ty, PointerKind::Unknown) => ty.to_doc().append(RcDoc::text("[?]")),
            TypeT::SpecInt => RcDoc::text("_specint"),
            TypeT::SpecNat => RcDoc::text("_specnat"),
            TypeT::SLProp => RcDoc::text("_slprop"),
            TypeT::TypeRef(n) => n.to_doc(),
            TypeT::Refine(ty, p) => RcDoc::text("_refine(")
                .append(p.to_doc())
                .append(")")
                .group()
                .nest(2)
                .append(RcDoc::line())
                .append(ty.to_doc()),
            TypeT::RefineAlways(ty, p) => RcDoc::text("_refine_always(")
                .append(p.to_doc())
                .append(")")
                .group()
                .nest(2)
                .append(RcDoc::line())
                .append(ty.to_doc()),
            TypeT::RefineUninit(ty, p) => RcDoc::text("_refine_uninit(")
                .append(p.to_doc())
                .append(")")
                .group()
                .nest(2)
                .append(RcDoc::line())
                .append(ty.to_doc()),
            TypeT::RefineValue(ty, binding_name, binding_ty, p) => RcDoc::text("_refine_value(")
                .append(binding_ty.to_doc())
                .append(" ")
                .append(RcDoc::text(binding_name.val.to_string()))
                .append(", ")
                .append(p.to_doc())
                .append(")")
                .group()
                .nest(2)
                .append(RcDoc::line())
                .append(ty.to_doc()),
            TypeT::Plain(ty) => RcDoc::text("_plain")
                .append(RcDoc::line())
                .append(ty.to_doc()),
            TypeT::Unknown => RcDoc::text("?unknown"),
            TypeT::Error => RcDoc::text("???"),
        }
    }
}

impl_display_using_prettyir!(ExprT);

impl PrettyIR for ExprT {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            // LValue variants
            ExprT::Var(x) => x.to_doc(),
            ExprT::Deref(rval) => RcDoc::text("(*").append(rval.to_doc()).append(")"),
            ExprT::Member(x, n) => x.to_doc().append(RcDoc::text(".")).append(n.to_doc()),
            ExprT::VAttr(VAttr::Length, x) => x.to_doc().append(RcDoc::text("._length")),
            ExprT::VAttr(VAttr::Active(fld), x) => x
                .to_doc()
                .append(RcDoc::text("."))
                .append(fld.to_doc())
                .append(RcDoc::text("._active")),
            ExprT::Index(arr, idx) => arr
                .to_doc()
                .append("[")
                .append(idx.to_doc())
                .append("]")
                .nest(2)
                .group(),

            // RValue variants
            ExprT::BoolLit(b) => RcDoc::text(if *b { "true" } else { "false" }),
            ExprT::IntLit(n, _ty) => RcDoc::text(n.to_string()),
            ExprT::Ref(lval) => RcDoc::text("&").append(lval.to_doc()),
            ExprT::UnOp(un_op, arg) => RcDoc::text(un_op.to_str()).append(arg.to_doc()),
            ExprT::BinOp(bin_op, lhs, rhs) => RcDoc::text("(")
                .append(lhs.to_doc())
                .append(RcDoc::space())
                .append(bin_op.to_str())
                .group()
                .append(RcDoc::line())
                .append(rhs.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::FnCall(f, args) => f
                .to_doc()
                .append("(")
                .append(RcDoc::intersperse(
                    args.iter().map(|arg| arg.to_doc()),
                    RcDoc::text(",").append(RcDoc::line()),
                ))
                .append(")")
                .group(),
            ExprT::Cast(rval, ty) => (RcDoc::text("(").append(ty.to_doc()).append(")"))
                .append(RcDoc::line())
                .append(rval.to_doc())
                .nest(2)
                .group(),
            ExprT::InlinePulse(inline_code, ty) => (RcDoc::text("(")
                .append(ty.to_doc())
                .append(")")
                .nest(2)
                .group())
            .append(RcDoc::line())
            .append(RcDoc::text("_inline_pulse("))
            .append(inline_pulse_code_to_doc(inline_code))
            .append(RcDoc::text(")"))
            .nest(2)
            .group(),
            ExprT::Live(v) => RcDoc::text("_live(")
                .append(v.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::Old(v) => RcDoc::text("_old(")
                .append(v.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::Forall(var, ty, body) => RcDoc::text("_forall(")
                .append(ty.to_doc())
                .append(RcDoc::space())
                .append(var.to_doc())
                .append(", ")
                .append(body.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::Exists(var, ty, body) => RcDoc::text("_exists(")
                .append(ty.to_doc())
                .append(RcDoc::space())
                .append(var.to_doc())
                .append(", ")
                .append(body.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::Error(_) => RcDoc::text("???"),
            ExprT::Malloc(ty) => RcDoc::text("malloc(sizeof(")
                .append(ty.to_doc())
                .append("))")
                .nest(4)
                .group(),
            ExprT::MallocArray(ty, count) => RcDoc::text("malloc(sizeof(")
                .append(ty.to_doc())
                .nest(2)
                .append(") * ")
                .append(count.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::Calloc(ty) => RcDoc::text("calloc(1, sizeof(")
                .append(ty.to_doc())
                .append("))")
                .nest(4)
                .group(),
            ExprT::CallocArray(ty, count) => RcDoc::text("calloc(")
                .append(count.to_doc())
                .append(", sizeof(")
                .append(ty.to_doc())
                .append("))")
                .nest(4)
                .group(),
            ExprT::Free(val) => RcDoc::text("free(")
                .append(val.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::PreIncr(val) => RcDoc::text("++").append(val.to_doc()),
            ExprT::PostIncr(val) => val.to_doc().append("++"),
            ExprT::PreDecr(val) => RcDoc::text("--").append(val.to_doc()),
            ExprT::PostDecr(val) => val.to_doc().append("--"),
            ExprT::StructInit(name, fields) => RcDoc::text("(")
                .append(name.to_doc())
                .append(") {")
                .append(RcDoc::intersperse(
                    fields.iter().map(|(fld, val)| {
                        RcDoc::text(".")
                            .append(fld.to_doc())
                            .append(" = ")
                            .append(val.to_doc())
                    }),
                    RcDoc::text(",").append(RcDoc::line()),
                ))
                .append("}")
                .nest(2)
                .group(),
            ExprT::UnionInit(name, fld, val) => RcDoc::text("(union ")
                .append(name.to_doc())
                .append("){.")
                .append(fld.to_doc())
                .append(" = ")
                .append(val.to_doc())
                .append("}")
                .nest(2)
                .group(),
            ExprT::Cond(cond, then_expr, else_expr) => RcDoc::text("(")
                .append(cond.to_doc())
                .append(" ? ")
                .append(then_expr.to_doc())
                .append(" : ")
                .append(else_expr.to_doc())
                .append(")")
                .nest(2)
                .group(),
            ExprT::AssignExpr(lhs, rhs) => RcDoc::text("(")
                .append(lhs.to_doc())
                .append(" = ")
                .append(rhs.to_doc())
                .append(")")
                .nest(2)
                .group(),
        }
    }
}

fn pretty_block(stmts: &Stmts) -> RcDoc<'_, ()> {
    if stmts.is_empty() {
        RcDoc::text("{}")
    } else {
        RcDoc::text("{")
            .append(RcDoc::hardline())
            .append(stmts.to_doc())
            .nest(2)
            .append(RcDoc::hardline())
            .append("}")
            .group()
    }
}

impl_display_using_prettyir!(StmtT);

impl PrettyIR for StmtT {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            StmtT::Call(f) => f.to_doc().append(";"),
            StmtT::Decl(x, ty) => (ty.to_doc())
                .append(" ")
                .append(x.to_doc())
                .append(";")
                .nest(2)
                .group(),
            StmtT::DeclStackArray {
                name,
                elem_type,
                size,
            } => (elem_type.to_doc())
                .append(" ")
                .append(name.to_doc())
                .append("[")
                .append(size.to_doc())
                .append("];")
                .nest(2)
                .group(),
            StmtT::Assign(x, v) => (x.to_doc())
                .append(" =")
                .append(RcDoc::line())
                .append(v.to_doc())
                .append(";")
                .nest(2)
                .group(),
            StmtT::If(c, b1, b2) => RcDoc::text("if (")
                .append(c.to_doc().nest(4))
                .append(") ")
                .append(pretty_block(b1))
                .append(" else ")
                .append(pretty_block(b2))
                .group(),
            StmtT::While {
                cond,
                inv,
                requires,
                ensures,
                body,
            } => RcDoc::text("while (")
                .append(cond.to_doc().nest(4))
                .append(")")
                .append(
                    RcDoc::concat(inv.iter().map(|inv| {
                        RcDoc::line().append(
                            RcDoc::text("_invariant(")
                                .append(RcDoc::line_())
                                .append(inv.to_doc())
                                .nest(2)
                                .append(")")
                                .group(),
                        )
                    }))
                    .append(RcDoc::concat(requires.iter().map(|r| {
                        RcDoc::line().append(
                            RcDoc::text("_requires(")
                                .append(RcDoc::line_())
                                .append(r.to_doc())
                                .nest(2)
                                .append(")")
                                .group(),
                        )
                    })))
                    .append(RcDoc::concat(ensures.iter().map(|e| {
                        RcDoc::line().append(
                            RcDoc::text("_ensures(")
                                .append(RcDoc::line_())
                                .append(e.to_doc())
                                .nest(2)
                                .append(")")
                                .group(),
                        )
                    })))
                    .nest(2),
                )
                .append(RcDoc::hardline())
                .append(pretty_block(body))
                .group(),
            StmtT::Break => RcDoc::text("break;"),
            StmtT::Continue => RcDoc::text("continue;"),
            StmtT::Return(Some(v)) => RcDoc::text("return")
                .append(RcDoc::line())
                .append(v.to_doc())
                .append(";")
                .nest(2)
                .group(),
            StmtT::Return(None) => RcDoc::text("return;"),
            StmtT::Assert(v) => RcDoc::text("_assert(")
                .append(v.to_doc())
                .append(");")
                .nest(2)
                .group(),
            StmtT::GhostStmt(code) => RcDoc::text("_ghost_stmt(")
                .append(inline_pulse_code_to_doc(code))
                .append(");")
                .nest(2)
                .group(),
            StmtT::Goto(label) => RcDoc::text("goto ")
                .append(RcDoc::text(label.val.to_string()))
                .append(";"),
            StmtT::Label { name, .. } => RcDoc::text(name.val.to_string()).append(":"),
            StmtT::GotoBlock {
                body,
                label,
                ensures,
            } => {
                let mut doc = pretty_block(body);
                for e in ensures.iter() {
                    doc = doc
                        .append(RcDoc::hardline())
                        .append("ensures ")
                        .append(e.to_doc());
                }
                doc.append(RcDoc::hardline())
                    .append(RcDoc::text(label.val.to_string()))
                    .append(":")
            }
            StmtT::Error => RcDoc::text("???;"),
        }
    }
}

impl PrettyIR for Stmts {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::intersperse(self.iter().map(|stmt| stmt.to_doc()), RcDoc::hardline()).group()
    }
}

impl PrettyIR for StructDefn {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::text("struct ")
            .append(self.name.to_doc())
            .append(" {")
            .append(RcDoc::line_())
            .append(RcDoc::concat(self.fields.iter().map(|f| {
                f.1.to_doc()
                    .append(RcDoc::line())
                    .append(f.0.to_doc())
                    .append(";")
                    .group()
                    .nest(2)
                    .append(RcDoc::hardline())
            })))
            .group()
            .nest(2)
            .append("};")
    }
}

impl PrettyIR for UnionDefn {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::text("union ")
            .append(self.name.to_doc())
            .append(" {")
            .append(RcDoc::line_())
            .append(RcDoc::concat(self.fields.iter().map(|f| {
                f.1.to_doc()
                    .append(RcDoc::line())
                    .append(f.0.to_doc())
                    .append(";")
                    .group()
                    .nest(2)
                    .append(RcDoc::hardline())
            })))
            .group()
            .nest(2)
            .append("};")
    }
}

impl PrettyIR for FnDecl {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        let pure_prefix = if self.is_pure {
            RcDoc::text("_pure").append(RcDoc::line())
        } else if self.is_rec {
            RcDoc::text("_rec").append(RcDoc::line())
        } else {
            RcDoc::nil()
        };
        pure_prefix
            .append(self.ret_type.to_doc())
            .append(RcDoc::line())
            .append(self.name.to_doc())
            .append("(")
            .append(
                RcDoc::intersperse(
                    self.args.iter().map(|arg| {
                        let mode_prefix = match arg.mode {
                            ParamMode::Consumed => RcDoc::text("_consumes").append(RcDoc::line()),
                            ParamMode::Const => RcDoc::text("_const").append(RcDoc::line()),
                            ParamMode::Out => RcDoc::text("_out").append(RcDoc::line()),
                            ParamMode::Regular => RcDoc::nil(),
                        };
                        mode_prefix
                            .append(arg.ty.to_doc())
                            .append(match &arg.name {
                                Some(n) => RcDoc::line().append(n.to_doc()),
                                None => RcDoc::nil(),
                            })
                            .group()
                            .nest(2)
                    }),
                    RcDoc::text(",").append(RcDoc::line()),
                )
                .group()
                .nest(2),
            )
            .append(")")
            .group()
            .append(RcDoc::concat(self.ghost_args.iter().map(|ga| {
                RcDoc::hardline().append(
                    RcDoc::text("_ghost_arg(")
                        .append(ga.ty.to_doc())
                        .append(RcDoc::line())
                        .append(ga.name.to_doc())
                        .append(")")
                        .group()
                        .nest(2),
                )
            })))
            .append(RcDoc::concat(self.requires.iter().map(|req| {
                RcDoc::hardline().append(
                    RcDoc::text("_requires(")
                        .append(req.to_doc())
                        .append(")")
                        .group()
                        .nest(2),
                )
            })))
            .append(RcDoc::concat(self.ensures.iter().map(|ens| {
                RcDoc::hardline().append(
                    RcDoc::text("_ensures(")
                        .append(ens.to_doc())
                        .append(")")
                        .group()
                        .nest(2),
                )
            })))
            .nest(2)
            .group()
    }
}

impl PrettyIR for FnDefn {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        self.decl
            .to_doc()
            .append(RcDoc::hardline())
            .append(pretty_block(&self.body))
    }
}

impl PrettyIR for TypeDefn {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::text("typedef")
            .append(RcDoc::line())
            .append(self.body.to_doc())
            .append(RcDoc::line())
            .append(self.name.to_doc())
            .append(";")
            .group()
            .nest(2)
    }
}

impl PrettyIR for IncludeDecl {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::text("_include_pulse(")
            .append(RcDoc::hardline())
            .append(inline_pulse_code_to_doc(&self.code))
            .group()
            .nest(2)
            .append(RcDoc::hardline())
            .append(")")
    }
}

impl PrettyIR for LetDecl {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        let keyword = if self.is_impure {
            "_letimpure("
        } else if self.is_rec {
            "_let_rec("
        } else {
            "_let("
        };
        let params = RcDoc::intersperse(
            self.params.iter().map(|arg| {
                let mode_prefix = match arg.mode {
                    ParamMode::Consumed => RcDoc::text("_consumes").append(RcDoc::line()),
                    ParamMode::Const => RcDoc::text("_const").append(RcDoc::line()),
                    ParamMode::Out => RcDoc::text("_out").append(RcDoc::line()),
                    ParamMode::Regular => RcDoc::nil(),
                };
                mode_prefix
                    .append(arg.ty.to_doc())
                    .append(match &arg.name {
                        Some(n) => RcDoc::line().append(n.to_doc()),
                        None => RcDoc::nil(),
                    })
                    .group()
                    .nest(2)
            }),
            RcDoc::text(", "),
        );
        RcDoc::text(keyword)
            .append(self.ret_type.to_doc())
            .append(" ")
            .append(self.name.to_doc())
            .append("(")
            .append(params)
            .append(")")
            .append(RcDoc::concat(self.requires.iter().map(|r| {
                RcDoc::line()
                    .append("_requires(")
                    .append(r.to_doc())
                    .append(")")
            })))
            .append(RcDoc::concat(self.ensures.iter().map(|e| {
                RcDoc::line()
                    .append("_ensures(")
                    .append(e.to_doc())
                    .append(")")
            })))
            .append(", ")
            .append(self.body.to_doc())
            .append(")")
    }
}

impl PrettyIR for GlobalVar {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        let prefix = if self.is_pure {
            RcDoc::text("_pure ")
        } else {
            RcDoc::nil()
        };
        let init = match &self.init {
            Some(e) => RcDoc::text(" = ").append(e.to_doc()),
            None => RcDoc::nil(),
        };
        prefix
            .append(self.ty.to_doc())
            .append(RcDoc::line())
            .append(self.name.to_doc())
            .append(init)
            .append(";")
            .group()
            .nest(2)
    }
}

impl PrettyIR for DeclT {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            DeclT::FnDefn(fn_defn) => fn_defn.to_doc(),
            DeclT::FnDecl(fn_decl) => fn_decl.to_doc(),
            DeclT::Typedef(type_defn) => type_defn.to_doc(),
            DeclT::StructDefn(struct_defn) => struct_defn.to_doc(),
            DeclT::StructDecl(name) => RcDoc::text("struct ")
                .append(name.to_doc())
                .append(RcDoc::text(";")),
            DeclT::UnionDefn(union_defn) => union_defn.to_doc(),
            DeclT::IncludeDecl(include_decl) => include_decl.to_doc(),
            DeclT::LetDecl(let_decl) => let_decl.to_doc(),
            DeclT::OpaqueTypeDecl(decl) => RcDoc::text("_type(")
                .append(decl.name.to_doc())
                .append(", ")
                .append(inline_pulse_code_to_doc(&decl.code))
                .append(")"),
            DeclT::GlobalVar(global_var) => global_var.to_doc(),
        }
    }
}

impl_display_using_prettyir!(TranslationUnit);

impl PrettyIR for TranslationUnit {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        let header_comment = RcDoc::text("// ").append(RcDoc::intersperse(
            self.main_file_names
                .iter()
                .map(|f| RcDoc::text(f.to_string())),
            RcDoc::text(", "),
        ));

        RcDoc::intersperse(
            std::iter::once(header_comment)
                .chain(self.decls.iter().map(|decl| decl.to_doc()))
                .map(|doc| doc.append(RcDoc::hardline())),
            RcDoc::hardline(),
        )
    }
}
