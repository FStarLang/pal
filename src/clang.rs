use num_bigint::BigInt;

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    hauntedc::{
        SnippetMap, TargetIntWidths, parse_expr, parse_ghost_arg_binding, parse_let_signature,
        parse_refine_value_binding, parse_type_name, process_inline_pulse,
    },
    ir::*,
    vfs::VFS,
};
use core::slice;
use std::{collections::HashSet, rc::Rc, str::FromStr};

mod generated {
    use crate::vfs::VFS;
    use std::ops::Deref;
    include!(concat!(env!("OUT_DIR"), "/generated.rs"));
}

unsafe fn str_from_parts<'a>(ptr: *const u8, sz: usize) -> &'a str {
    str::from_utf8(unsafe { slice::from_raw_parts(ptr, sz) }).unwrap()
}

pub struct Ctx<'a> {
    vfs: &'a mut dyn VFS,
    input_file_name: String,
    include_paths: Vec<String>,
    interned_strs: HashSet<Rc<str>>,
    translation_unit: TranslationUnit,
    diagnostics: Diagnostics,
    target_int_widths: TargetIntWidths,
}

impl<'a> Ctx<'a> {
    fn new(input_file_name: String, include_paths: Vec<String>, vfs: &'a mut dyn VFS) -> Ctx<'a> {
        let input_fn: &str = &input_file_name;
        let main_file_name: Rc<str> = Rc::from(input_fn);
        Ctx {
            vfs,
            input_file_name,
            include_paths,
            interned_strs: HashSet::new(),
            translation_unit: TranslationUnit {
                main_file_names: vec![main_file_name],
                decls: vec![],
            },
            diagnostics: Diagnostics::empty(),
            target_int_widths: TargetIntWidths::default(),
        }
    }

    fn get_input_file_name(&self) -> &str {
        &self.input_file_name
    }

    fn get_include_path_count(&self) -> usize {
        self.include_paths.len()
    }

    fn get_include_path(&self, idx: usize) -> &str {
        &self.include_paths[idx]
    }

    fn set_target_int_widths(&mut self, widths: TargetIntWidths) {
        self.target_int_widths = widths;
    }

    fn intern_str(&mut self, s: &str) -> Rc<str> {
        match self.interned_strs.get(s) {
            Some(s) => s.clone(),
            None => {
                let s: Rc<str> = Rc::from(s);
                self.interned_strs.insert(s.clone());
                s
            }
        }
    }

    fn mk_ident(&mut self, name: &str, loc: Rc<SourceInfo>) -> Rc<Ident> {
        Rc::new(Ast {
            val: self.intern_str(name),
            loc: loc,
        })
    }

    fn add_fn_decl(&mut self, builder: DeclBuilder) {
        self.translation_unit.decls.push(Ast {
            loc: builder.loc,
            val: DeclT::FnDecl(FnDecl {
                name: builder.name,
                ret_type: builder.ret_type.unwrap(),
                args: builder.args,
                ghost_args: builder.ghost_args,
                requires: builder.requires,
                ensures: builder.ensures,
                is_pure: builder.is_pure,
                is_rec: builder.is_rec,
                is_total: builder.is_total,
                decreases: builder.decreases,
            }),
        })
    }

    fn add_fn_defn(&mut self, builder: DeclBuilder, body: Vec<Rc<Stmt>>) {
        self.translation_unit.decls.push(Ast {
            loc: builder.loc,
            val: DeclT::FnDefn(FnDefn {
                decl: FnDecl {
                    name: builder.name,
                    ret_type: builder.ret_type.unwrap(),
                    args: builder.args,
                    ghost_args: builder.ghost_args,
                    requires: builder.requires,
                    ensures: builder.ensures,
                    is_pure: builder.is_pure,
                    is_rec: builder.is_rec,
                    is_total: builder.is_total,
                    decreases: builder.decreases,
                },
                body: body,
            }),
        })
    }

    fn add_typedef(
        &mut self,
        loc: Rc<SourceInfo>,
        name: Rc<Ident>,
        body: Rc<Type>,
        is_pointer_view: bool,
    ) {
        self.translation_unit.decls.push(Ast {
            loc,
            val: DeclT::Typedef(TypeDefn {
                name,
                body,
                is_pointer_view,
            }),
        })
    }

    fn add_struct(&mut self, builder: DeclBuilder) {
        self.translation_unit.decls.push(Ast {
            loc: builder.loc,
            val: DeclT::StructDefn(StructDefn {
                name: builder.name,
                refines: builder.refines.unwrap(),
                fields: builder.fields,
                eager_unfold_pred: builder.eager_unfold_pred,
            }),
        })
    }

    fn add_struct_decl(&mut self, loc: Rc<SourceInfo>, name: Rc<Ident>) {
        self.translation_unit.decls.push(Ast {
            loc,
            val: DeclT::StructDecl(name),
        })
    }

    fn add_union(&mut self, builder: DeclBuilder) {
        self.translation_unit.decls.push(Ast {
            loc: builder.loc,
            val: DeclT::UnionDefn(UnionDefn {
                name: builder.name,
                fields: builder.fields,
            }),
        })
    }

    fn add_global_var(
        &mut self,
        loc: Rc<SourceInfo>,
        name: Rc<Ident>,
        ty: Rc<Type>,
        init: Option<Rc<Expr>>,
        is_pure: bool,
        is_extern: bool,
        opaque_to_smt: bool,
        is_enum_constant: bool,
    ) {
        self.translation_unit.decls.push(Ast {
            loc,
            val: DeclT::GlobalVar(GlobalVar {
                name,
                ty,
                init,
                is_pure,
                is_extern,
                opaque_to_smt,
                is_enum_constant,
            }),
        })
    }

    fn add_include(
        &mut self,
        loc: Rc<SourceInfo>,
        module_name: &str,
        idx: u32,
        snippets: &SnippetMap,
    ) {
        match snippets.snippets.get(&idx) {
            Some(code) => {
                let pulse_code = process_inline_pulse(
                    &mut self.diagnostics,
                    &loc,
                    code,
                    snippets,
                    &self.target_int_widths,
                );
                let module_name: Rc<str> = Rc::from(module_name);
                self.translation_unit.decls.push(Ast {
                    loc,
                    val: DeclT::IncludeDecl(IncludeDecl {
                        module_name,
                        code: pulse_code,
                    }),
                })
            }
            None => self.report_diag(loc, true, "internal error: invalid inline_pulse encoding"),
        }
    }

    fn add_let_decl(
        &mut self,
        loc: Rc<SourceInfo>,
        is_rec: bool,
        sig_idx: u32,
        body_idx: u32,
        snippets: &SnippetMap,
    ) {
        self.add_let_decl_inner(loc, is_rec, false, sig_idx, body_idx, snippets);
    }

    fn add_letimpure_decl(
        &mut self,
        loc: Rc<SourceInfo>,
        sig_idx: u32,
        body_idx: u32,
        snippets: &SnippetMap,
    ) {
        self.add_let_decl_inner(loc, false, true, sig_idx, body_idx, snippets);
    }

    fn add_let_decl_inner(
        &mut self,
        loc: Rc<SourceInfo>,
        is_rec: bool,
        is_impure: bool,
        sig_idx: u32,
        body_idx: u32,
        snippets: &SnippetMap,
    ) {
        let sig_code = match snippets.snippets.get(&sig_idx) {
            Some(code) => code,
            None => {
                self.report_diag(loc, true, "internal error: invalid _let signature encoding");
                return;
            }
        };
        let body_code = match snippets.snippets.get(&body_idx) {
            Some(code) => code,
            None => {
                self.report_diag(loc, true, "internal error: invalid _let body encoding");
                return;
            }
        };

        let (name, ret_type, params, requires, ensures) = match parse_let_signature(
            &mut self.diagnostics,
            &loc,
            sig_code,
            snippets,
            &self.target_int_widths,
        ) {
            Some(result) => result,
            None => return,
        };

        let body = parse_expr(
            &mut self.diagnostics,
            &loc,
            body_code,
            snippets,
            &self.target_int_widths,
        );

        self.translation_unit.decls.push(Ast {
            loc,
            val: DeclT::LetDecl(LetDecl {
                name,
                is_rec,
                is_impure,
                ret_type,
                params,
                requires,
                ensures,
                body,
            }),
        });
    }

    fn add_type_decl(
        &mut self,
        loc: Rc<SourceInfo>,
        name_idx: u32,
        body_idx: u32,
        snippets: &SnippetMap,
    ) {
        let name_code = match snippets.snippets.get(&name_idx) {
            Some(code) => code,
            None => {
                self.report_diag(loc, true, "internal error: invalid _type name encoding");
                return;
            }
        };
        let body_code = match snippets.snippets.get(&body_idx) {
            Some(code) => code,
            None => {
                self.report_diag(loc, true, "internal error: invalid _type body encoding");
                return;
            }
        };

        let name = match parse_type_name(&mut self.diagnostics, &loc, name_code) {
            Some(name) => name,
            None => return,
        };

        let code = process_inline_pulse(
            &mut self.diagnostics,
            &loc,
            body_code,
            snippets,
            &self.target_int_widths,
        );

        self.translation_unit.decls.push(Ast {
            loc,
            val: DeclT::OpaqueTypeDecl(OpaqueTypeDecl { name, code }),
        });
    }

    fn mk_ghost_stmt(&mut self, loc: Rc<SourceInfo>, idx: u32, snippets: &SnippetMap) -> Rc<Stmt> {
        match snippets.snippets.get(&idx) {
            Some(code) => {
                let pulse_code = process_inline_pulse(
                    &mut self.diagnostics,
                    &loc,
                    code,
                    snippets,
                    &self.target_int_widths,
                );
                mk_ast(loc, StmtT::GhostStmt(Rc::new(pulse_code)))
            }
            None => {
                self.report_diag(loc.clone(), true, "internal error: invalid code snippet");
                mk_ast(loc, StmtT::Error)
            }
        }
    }

    fn parse_ghost_arg(
        &mut self,
        builder: &mut DeclBuilder,
        loc: Rc<SourceInfo>,
        idx: u32,
        snippets: &SnippetMap,
    ) {
        match snippets.snippets.get(&idx) {
            Some(code) => {
                if let Some((name, ty)) = parse_ghost_arg_binding(
                    &mut self.diagnostics,
                    &loc,
                    code,
                    &self.target_int_widths,
                ) {
                    builder.ghost_arg(name, ty);
                }
            }
            None => {
                self.report_diag(loc, true, "internal error: invalid ghost_arg encoding");
            }
        }
    }

    /// Attach the ghost args accumulated in `builder` to a function-pointer
    /// type. See `TypeT::FnPtr` for why the type carries them at all.
    fn fnptr_with_ghost_args(&mut self, ty: Rc<Type>, builder: &mut DeclBuilder) -> Rc<Type> {
        if builder.ghost_args.is_empty() {
            return ty;
        }
        // A `_refine`, `_plain`, `_nullable` etc. on the same declaration wraps
        // the function-pointer type, so descend through the wrappers and
        // rebuild them around the annotated inner type. `trTypeAttrs` applies
        // these by attribute name without consulting the underlying type, so
        // any of them can sit on a function-pointer declaration.
        macro_rules! rewrap {
            ($ctor:path, $inner:expr $(, $rest:expr)*) => {{
                let inner = self.fnptr_with_ghost_args($inner.clone(), builder);
                return mk_ast(ty.loc.clone(), $ctor(inner $(, $rest.clone())*));
            }};
        }
        match &ty.val {
            TypeT::FnPtr { args, ret, .. } => mk_ast(
                ty.loc.clone(),
                TypeT::FnPtr {
                    args: args.clone(),
                    ret: ret.clone(),
                    ghost_args: std::mem::take(&mut builder.ghost_args),
                },
            ),
            TypeT::Refine(inner, p) => rewrap!(TypeT::Refine, inner, p),
            TypeT::RefineAlways(inner, p) => rewrap!(TypeT::RefineAlways, inner, p),
            TypeT::RefineUninit(inner, p) => rewrap!(TypeT::RefineUninit, inner, p),
            TypeT::RefineValue(inner, n, t, p) => rewrap!(TypeT::RefineValue, inner, n, t, p),
            TypeT::Plain(inner) => rewrap!(TypeT::Plain, inner),
            TypeT::Nullable(inner) => rewrap!(TypeT::Nullable, inner),
            _ => {
                self.report_diag(
                    ty.loc.clone(),
                    true,
                    "_ghost_arg is only supported on function-pointer declarations",
                );
                ty
            }
        }
    }

    fn parse_rvalue(&mut self, loc: Rc<SourceInfo>, idx: u32, snippets: &SnippetMap) -> Rc<Expr> {
        match snippets.snippets.get(&idx) {
            Some(code) => parse_expr(
                &mut self.diagnostics,
                &loc,
                code,
                snippets,
                &self.target_int_widths,
            ),
            None => {
                self.report_diag(loc.clone(), true, "internal error: invalid code snippet");
                ExprT::Error(TypeT::Error.with_loc(loc.clone())).with_loc(loc)
            }
        }
    }

    fn report_diag(&mut self, loc: Rc<SourceInfo>, is_err: bool, msg: &str) {
        self.diagnostics.report(Diagnostic {
            loc: (match &*loc {
                SourceInfo::Original(loc) => loc.clone(),
                _ => panic!(),
            }),
            level: (if is_err {
                DiagnosticLevel::Error
            } else {
                DiagnosticLevel::Warning
            }),
            msg: msg.into(),
        })
    }
}

impl<'a> VFS for Ctx<'a> {
    fn read_vfs_file(&mut self, file_name: &str) -> crate::vfs::VFSResult {
        self.vfs.read_vfs_file(file_name)
    }
}

struct DeclBuilder {
    name: Rc<Ident>,
    loc: Rc<SourceInfo>,
    ret_type: Option<Rc<Type>>,
    args: Vec<FnArg>,
    ghost_args: Vec<GhostArg>,
    fields: Vec<Field>,
    refines: Option<Rc<Type>>,
    requires: Vec<Rc<Expr>>,
    ensures: Vec<Rc<Expr>>,
    is_pure: bool,
    is_rec: bool,
    is_total: bool,
    decreases: Option<Rc<Expr>>,
    eager_unfold_pred: bool,
}

impl DeclBuilder {
    fn new(loc: Rc<SourceInfo>, name: Rc<Ident>) -> DeclBuilder {
        DeclBuilder {
            name,
            loc,
            ret_type: None,
            args: vec![],
            ghost_args: vec![],
            fields: vec![],
            refines: None,
            requires: vec![],
            ensures: vec![],
            is_pure: false,
            is_rec: false,
            is_total: false,
            decreases: None,
            eager_unfold_pred: false,
        }
    }

    fn return_type(&mut self, ret_type: Rc<Type>) {
        self.ret_type = Some(ret_type);
    }

    fn arg(&mut self, name: Rc<Ident>, ty: Rc<Type>, mode: ParamMode) {
        self.args.push(FnArg {
            name: Some(name),
            ty,
            mode,
        })
    }
    fn arg_anon(&mut self, ty: Rc<Type>, mode: ParamMode) {
        self.args.push(FnArg {
            name: None,
            ty,
            mode,
        })
    }

    fn field(&mut self, name: Rc<Ident>, ty: Rc<Type>) {
        let loc = name.loc.clone();
        self.fields.push(Ast {
            loc,
            val: FieldT::Plain {
                name: (*name).clone(),
                ty,
            },
        })
    }

    fn field_bitfield(&mut self, name: Rc<Ident>, ty: Rc<Type>, width: u32) {
        let loc = name.loc.clone();
        self.fields.push(Ast {
            loc,
            val: FieldT::BitField {
                name: (*name).clone(),
                ty,
                width,
            },
        })
    }

    fn refines(&mut self, ty: Rc<Type>) {
        self.refines = Some(ty);
    }

    fn requires(&mut self, p: Rc<Expr>) {
        self.requires.push(p)
    }
    fn ensures(&mut self, p: Rc<Expr>) {
        self.ensures.push(p)
    }
    fn set_pure(&mut self) {
        self.is_pure = true;
    }
    fn set_rec(&mut self) {
        self.is_rec = true;
    }
    fn set_total(&mut self) {
        self.is_total = true;
    }
    fn set_eager_unfold_pred(&mut self) {
        self.eager_unfold_pred = true;
    }
    fn decreases(&mut self, p: Rc<Expr>) {
        self.decreases = Some(p);
    }
    fn ghost_arg(&mut self, name: Rc<Ident>, ty: Rc<Type>) {
        self.ghost_args.push(GhostArg { name, ty })
    }
}

struct InlineCodeBuilder(InlineCode);

impl InlineCodeBuilder {
    fn new() -> InlineCodeBuilder {
        InlineCodeBuilder(InlineCode { tokens: vec![] })
    }
    fn push_token(&mut self, before: &'static str, loc: Rc<SourceInfo>, tok: &str) {
        self.0.tokens.push(CodeToken {
            before: before,
            text: Ast {
                val: Rc::from(tok),
                loc: loc,
            },
        })
    }
    fn insert_into_map(self, idx: u32, snippets: &mut SnippetMap) {
        snippets.snippets.insert(idx, self.0);
    }
}

fn mk_original_location(
    file_name: Rc<str>,
    start_line: u32,
    start_char: u32,
    end_line: u32,
    end_char: u32,
) -> Rc<SourceInfo> {
    Rc::new(SourceInfo::Original(Location {
        file_name: file_name,
        range: Range {
            start: Position {
                line: start_line,
                character: start_char,
            },
            end: Position {
                line: end_line,
                character: end_char,
            },
        },
    }))
}
fn mk_fallback_sourceinfo(loc: &Rc<SourceInfo>) -> Rc<SourceInfo> {
    match &**loc {
        SourceInfo::Original(location) => Rc::new(SourceInfo::Fallback(location.clone())),
        SourceInfo::Fallback(_) => loc.clone(),
    }
}

fn mk_ast<T>(loc: Rc<SourceInfo>, val: T) -> Rc<Ast<T>> {
    Rc::new(Ast { val: val, loc: loc })
}

fn mk_void_type(loc: Rc<SourceInfo>) -> Rc<Type> {
    mk_ast(loc, TypeT::Void)
}
fn mk_bool_type(loc: Rc<SourceInfo>) -> Rc<Type> {
    mk_ast(loc, TypeT::Bool)
}
fn mk_int_type(loc: Rc<SourceInfo>, signed: bool, width: u32) -> Rc<Type> {
    mk_ast(
        loc,
        TypeT::Int {
            signed: signed,
            width: width,
        },
    )
}
fn mk_float_type(loc: Rc<SourceInfo>, width: u32) -> Rc<Type> {
    mk_ast(loc, TypeT::Float { width })
}
fn mk_sizet(loc: Rc<SourceInfo>) -> Rc<Type> {
    mk_ast(loc, TypeT::SizeT)
}
fn mk_pointer_unknown(loc: Rc<SourceInfo>, to: Rc<Type>) -> Rc<Type> {
    mk_ast(loc, TypeT::Pointer(to, PointerKind::Unknown))
}
fn mk_pointer_array(loc: Rc<SourceInfo>, to: Rc<Type>) -> Rc<Type> {
    mk_ast(loc, TypeT::Pointer(to, PointerKind::Array))
}
fn mk_fixed_array_type(loc: Rc<SourceInfo>, elem_ty: Rc<Type>, length: u64) -> Rc<Type> {
    mk_ast(loc, TypeT::FixedArray(elem_ty, length))
}
fn mk_flex_array_type(loc: Rc<SourceInfo>, elem_ty: Rc<Type>) -> Rc<Type> {
    mk_ast(loc, TypeT::FlexArray(elem_ty))
}
fn mk_type_fnptr(loc: Rc<SourceInfo>, args: Vec<Rc<Type>>, ret: Rc<Type>) -> Rc<Type> {
    mk_ast(
        loc,
        TypeT::FnPtr {
            args,
            ret,
            ghost_args: vec![],
        },
    )
}
fn mk_type_struct(loc: Rc<SourceInfo>, n: Rc<Ident>) -> Rc<Type> {
    mk_ast(loc, TypeT::TypeRef(TypeRefKind::Struct(n)))
}
fn mk_type_union(loc: Rc<SourceInfo>, n: Rc<Ident>) -> Rc<Type> {
    mk_ast(loc, TypeT::TypeRef(TypeRefKind::Union(n)))
}
fn mk_type_typedef(loc: Rc<SourceInfo>, n: Rc<Ident>) -> Rc<Type> {
    mk_ast(loc, TypeT::TypeRef(TypeRefKind::Typedef(n)))
}
fn mk_type_refine(loc: Rc<SourceInfo>, ty: Rc<Type>, p: Rc<Expr>) -> Rc<Type> {
    TypeT::Refine(ty, p).with_loc(loc)
}
fn mk_type_refine_always(loc: Rc<SourceInfo>, ty: Rc<Type>, p: Rc<Expr>) -> Rc<Type> {
    TypeT::RefineAlways(ty, p).with_loc(loc)
}
fn mk_type_refine_uninit(loc: Rc<SourceInfo>, ty: Rc<Type>, p: Rc<Expr>) -> Rc<Type> {
    TypeT::RefineUninit(ty, p).with_loc(loc)
}
fn mk_type_refine_value(
    loc: Rc<SourceInfo>,
    ty: Rc<Type>,
    binding_idx: u32,
    pred_idx: u32,
    snippets: &SnippetMap,
) -> Rc<Type> {
    let binding_code = match snippets.snippets.get(&binding_idx) {
        Some(code) => code,
        None => return TypeT::Error.with_loc(loc),
    };
    let pred_code = match snippets.snippets.get(&pred_idx) {
        Some(code) => code,
        None => return TypeT::Error.with_loc(loc),
    };

    // We need a mutable Diagnostics for parsing — create a temporary one.
    // Errors will be lost here, but this is consistent with how other type
    // attribute helpers work (they report errors via the Ctx later).
    let mut diagnostics = Diagnostics::empty();

    let (binding_name, binding_type) =
        match parse_refine_value_binding(&mut diagnostics, &loc, binding_code) {
            Some(r) => r,
            None => return TypeT::Error.with_loc(loc),
        };

    let target_widths = TargetIntWidths::default();
    let pred = parse_expr(&mut diagnostics, &loc, pred_code, snippets, &target_widths);

    TypeT::RefineValue(ty, binding_name, binding_type, pred).with_loc(loc)
}
fn mk_type_plain(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Type> {
    TypeT::Plain(ty).with_loc(loc)
}
fn mk_type_nullable(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Type> {
    TypeT::Nullable(ty).with_loc(loc)
}
fn mk_type_array(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Type> {
    match &ty.val {
        TypeT::Pointer(elem, PointerKind::Unknown) => {
            TypeT::Pointer(elem.clone(), PointerKind::Array).with_loc(loc)
        }
        _ => {
            eprintln!("warning: _array on non-pointer type: {}", ty);
            ty
        }
    }
}
fn mk_type_arrayptr(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Type> {
    match &ty.val {
        TypeT::Pointer(elem, PointerKind::Unknown) => {
            TypeT::Pointer(elem.clone(), PointerKind::ArrayPtr).with_loc(loc)
        }
        _ => {
            eprintln!("warning: _arrayptr on non-pointer type: {}", ty);
            ty
        }
    }
}
fn mk_type_core_ref(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Type> {
    match &ty.val {
        TypeT::Pointer(elem, PointerKind::Unknown) => {
            TypeT::Pointer(elem.clone(), PointerKind::Core).with_loc(loc)
        }
        _ => {
            eprintln!("warning: _core_ref on non-pointer type: {}", ty);
            ty
        }
    }
}
fn mk_type_err(loc: Rc<SourceInfo>) -> Rc<Type> {
    mk_ast(loc, TypeT::Error)
}

fn mk_bigint(s: &str) -> Rc<BigInt> {
    Rc::from(BigInt::from_str(s).unwrap())
}

fn mk_bool_lit(loc: Rc<SourceInfo>, val: bool) -> Rc<Expr> {
    mk_ast(loc, ExprT::BoolLit(val))
}
fn mk_int_lit(loc: Rc<SourceInfo>, val: Rc<BigInt>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::IntLit(val, ty))
}
fn mk_float_lit(loc: Rc<SourceInfo>, val: Rc<str>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::FloatLit(val, ty))
}
fn mk_rvalue_lvalue(loc: Rc<SourceInfo>, lval: Rc<Expr>) -> Rc<Expr> {
    // With unified Expr, lvalue-to-rvalue is identity
    let _ = loc;
    lval
}
fn mk_rvalue_cast(loc: Rc<SourceInfo>, val: Rc<Expr>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Cast(val, ty))
}
fn mk_rvalue_unop(loc: Rc<SourceInfo>, op: UnOp, arg: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::UnOp(op, arg))
}
fn mk_rvalue_binop(loc: Rc<SourceInfo>, op: BinOp, lhs: Rc<Expr>, rhs: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::BinOp(op, lhs, rhs))
}
fn mk_rvalue_ref(loc: Rc<SourceInfo>, lval: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Ref(lval))
}
fn mk_rvalue_fncall(loc: Rc<SourceInfo>, f: Rc<Ident>, args: Vec<Rc<Expr>>) -> Rc<Expr> {
    ExprT::FnCall(f, args).with_loc(loc)
}
fn mk_rvalue_fnref(loc: Rc<SourceInfo>, f: Rc<Ident>) -> Rc<Expr> {
    ExprT::FnRef(f).with_loc(loc)
}
fn mk_rvalue_fnptr_call(loc: Rc<SourceInfo>, f: Rc<Expr>, args: Vec<Rc<Expr>>) -> Rc<Expr> {
    ExprT::FnPtrCall(f, args).with_loc(loc)
}
fn mk_cast(loc: Rc<SourceInfo>, val: Rc<Expr>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Cast(val, ty))
}
fn mk_container_of(
    loc: Rc<SourceInfo>,
    ptr: Rc<Expr>,
    struct_ty: Rc<Type>,
    field: Rc<Ident>,
) -> Rc<Expr> {
    mk_ast(loc, ExprT::ContainerOf(ptr, struct_ty, field))
}
fn mk_rvalue_err(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Error(ty))
}
fn mk_malloc(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Malloc(ty))
}
fn mk_malloc_array(loc: Rc<SourceInfo>, ty: Rc<Type>, count: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::MallocArray(ty, count))
}
fn mk_calloc(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Calloc(ty))
}
fn mk_calloc_array(loc: Rc<SourceInfo>, ty: Rc<Type>, count: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::CallocArray(ty, count))
}
fn mk_malloc_flex(loc: Rc<SourceInfo>, ty: Rc<Type>, count: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::MallocFlex(ty, count))
}
fn mk_calloc_flex(loc: Rc<SourceInfo>, ty: Rc<Type>, count: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::CallocFlex(ty, count))
}
fn mk_memset(
    loc: Rc<SourceInfo>,
    ty: Rc<Type>,
    ptr: Rc<Expr>,
    value: Rc<Expr>,
    count: Rc<Expr>,
) -> Rc<Expr> {
    mk_ast(loc, ExprT::Memset(ty, ptr, value, count))
}
fn mk_memset_zero(loc: Rc<SourceInfo>, ty: Rc<Type>, ptr: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::MemsetZero(ty, ptr))
}
fn mk_free(loc: Rc<SourceInfo>, val: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Free(val))
}
fn mk_pre_incr(loc: Rc<SourceInfo>, val: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::PreIncr(val))
}
fn mk_post_incr(loc: Rc<SourceInfo>, val: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::PostIncr(val))
}
fn mk_pre_decr(loc: Rc<SourceInfo>, val: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::PreDecr(val))
}
fn mk_post_decr(loc: Rc<SourceInfo>, val: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::PostDecr(val))
}
fn mk_cond(
    loc: Rc<SourceInfo>,
    cond: Rc<Expr>,
    then_expr: Rc<Expr>,
    else_expr: Rc<Expr>,
) -> Rc<Expr> {
    mk_ast(loc, ExprT::Cond(cond, then_expr, else_expr))
}
fn mk_live(loc: Rc<SourceInfo>, val: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Live(val))
}
fn mk_assign_expr(loc: Rc<SourceInfo>, lhs: Rc<Expr>, rhs: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::AssignExpr(lhs, rhs))
}
fn mk_sizeof(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::SizeOf(ty))
}
fn mk_alignof(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::AlignOf(ty))
}

pub struct StructInitBuilder {
    loc: Rc<SourceInfo>,
    name: Rc<Ident>,
    fields: Vec<(Rc<Ident>, Rc<Expr>)>,
}

impl StructInitBuilder {
    fn new(loc: Rc<SourceInfo>, name: Rc<Ident>) -> StructInitBuilder {
        StructInitBuilder {
            loc,
            name,
            fields: vec![],
        }
    }

    fn field(&mut self, name: Rc<Ident>, val: Rc<Expr>) {
        self.fields.push((name, val));
    }

    fn build(self) -> Rc<Expr> {
        ExprT::StructInit(self.name, self.fields).with_loc(self.loc)
    }
}

fn mk_union_init(loc: Rc<SourceInfo>, name: Rc<Ident>, fld: Rc<Ident>, val: Rc<Expr>) -> Rc<Expr> {
    ExprT::UnionInit(name, fld, val).with_loc(loc)
}

fn mk_array_init(
    loc: Rc<SourceInfo>,
    elem_ty: Rc<Type>,
    elems: Vec<Rc<Expr>>,
    is_static: bool,
) -> Rc<Expr> {
    ExprT::ArrayInit {
        elem_ty,
        elems,
        is_static,
    }
    .with_loc(loc)
}

fn mk_lvalue_var(loc: Rc<SourceInfo>, name: Rc<Ident>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Var(name))
}
fn mk_deref(loc: Rc<SourceInfo>, v: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Deref(v))
}
fn mk_lvalue_member(loc: Rc<SourceInfo>, v: Rc<Expr>, a: Rc<Ident>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Member(v, a))
}
fn mk_index(loc: Rc<SourceInfo>, base: Rc<Expr>, idx: Rc<Expr>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Index(base, idx))
}
fn mk_lvalue_err(loc: Rc<SourceInfo>, ty: Rc<Type>) -> Rc<Expr> {
    mk_ast(loc, ExprT::Error(ty))
}

fn mk_var_decl(loc: Rc<SourceInfo>, id: Rc<Ident>, ty: Rc<Type>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Decl(id, ty))
}
fn mk_let_stmt(loc: Rc<SourceInfo>, id: Rc<Ident>, ty: Rc<Type>, value: Rc<Expr>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Let(id, ty, value))
}
fn mk_decl_stack_array(
    loc: Rc<SourceInfo>,
    name: Rc<Ident>,
    elem_type: Rc<Type>,
    size: Rc<Expr>,
) -> Rc<Stmt> {
    mk_ast(
        loc,
        StmtT::DeclStackArray {
            name,
            elem_type,
            size,
        },
    )
}
fn mk_assign(loc: Rc<SourceInfo>, lhs: Rc<Expr>, rhs: Rc<Expr>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Assign(lhs, rhs))
}
fn mk_return(loc: Rc<SourceInfo>, v: Rc<Expr>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Return(Some(v)))
}
fn mk_return_void(loc: Rc<SourceInfo>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Return(None))
}
fn mk_call(loc: Rc<SourceInfo>, f: Rc<Expr>) -> Rc<Stmt> {
    StmtT::Call(f).with_loc(loc)
}
fn mk_if(loc: Rc<SourceInfo>, cond: Rc<Expr>, a: Stmts, b: Stmts, ensures: Exprs) -> Rc<Stmt> {
    StmtT::If {
        cond,
        then_branch: Rc::new(a),
        else_branch: Rc::new(b),
        ensures: Rc::new(ensures),
    }
    .with_loc(loc)
}
fn mk_match_branch(patterns: Exprs, body: Stmts) -> Rc<MatchBranch> {
    Rc::new(MatchBranch {
        patterns: Rc::new(patterns),
        body: Rc::new(body),
    })
}
fn mk_match(
    loc: Rc<SourceInfo>,
    scrutinee: Rc<Expr>,
    branches: Vec<Rc<MatchBranch>>,
    default_branch: Stmts,
    ensures: Exprs,
) -> Rc<Stmt> {
    StmtT::Match {
        scrutinee,
        branches: Rc::new(branches),
        default_branch: Rc::new(default_branch),
        ensures: Rc::new(ensures),
    }
    .with_loc(loc)
}
fn mk_while(
    loc: Rc<SourceInfo>,
    cond: Rc<Expr>,
    invs: Exprs,
    requires: Exprs,
    ensures: Exprs,
    body: Stmts,
) -> Rc<Stmt> {
    StmtT::While {
        cond,
        inv: Rc::new(invs),
        requires: Rc::new(requires),
        ensures: Rc::new(ensures),
        body: Rc::new(body),
    }
    .with_loc(loc)
}
fn mk_break(loc: Rc<SourceInfo>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Break)
}
fn mk_continue(loc: Rc<SourceInfo>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Continue)
}
fn mk_stmt_err(loc: Rc<SourceInfo>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Error)
}
fn mk_assert(loc: Rc<SourceInfo>, v: Rc<Expr>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Assert(v))
}
fn mk_goto(loc: Rc<SourceInfo>, label: Rc<Ident>) -> Rc<Stmt> {
    mk_ast(loc, StmtT::Goto(label))
}
fn mk_label(loc: Rc<SourceInfo>, label: Rc<Ident>, ensures: Exprs) -> Rc<Stmt> {
    StmtT::Label {
        name: label,
        ensures: Rc::new(ensures),
    }
    .with_loc(loc)
}

pub fn parse_file(
    file_name: &str,
    include_paths: &[String],
    vfs: &mut dyn VFS,
) -> (TranslationUnit, Diagnostics) {
    let mut ctx = Ctx::new(file_name.to_string(), include_paths.to_vec(), vfs);
    generated::parse_file(&mut ctx);
    (ctx.translation_unit, ctx.diagnostics)
}
