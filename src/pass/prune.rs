use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    rc::Rc,
};

use crate::ir::*;

struct Deps<T> {
    roots: HashSet<T>,
    deps: HashMap<T, HashSet<T>>,
}

impl<T: Eq + Hash> Deps<T> {
    fn new() -> Deps<T> {
        Deps {
            roots: HashSet::new(),
            deps: HashMap::new(),
        }
    }

    fn add_root(&mut self, root: T) {
        self.roots.insert(root);
    }

    fn deps_for(&mut self, from: T) -> &mut HashSet<T> {
        self.deps.entry(from).or_default()
    }

    fn propagate(&mut self) -> PropagatedDeps<'_, T> {
        let mut todo = vec![];
        for r in &self.roots {
            if let Some(t) = self.deps.remove(r) {
                todo.push(t);
            }
        }
        while let Some(next) = todo.pop() {
            for n in next {
                if let Some(t) = self.deps.remove(&n) {
                    todo.push(t);
                }
                self.roots.insert(n);
            }
        }
        PropagatedDeps(self)
    }
}

struct PropagatedDeps<'a, T>(&'a Deps<T>);
impl<'a, T: Eq + Hash> PropagatedDeps<'a, T> {
    #[inline]
    fn contains(&self, t: &T) -> bool {
        self.0.roots.contains(t)
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
enum DeclName {
    Fn(Rc<str>),
    Struct(Rc<str>),
    Union(Rc<str>),
    Typedef(Rc<str>),
    GlobalVar(Rc<str>),
    Include(Rc<SourceInfo>),
}

fn in_main_file(main_files: &[Rc<str>], loc: &SourceInfo) -> bool {
    main_files.iter().any(|mf| loc.location().file_name == *mf)
}

fn scan_type(deps: &mut HashSet<DeclName>, ty: &Type) {
    match &ty.val {
        TypeT::Int {
            signed: _,
            width: _,
        } => {}
        TypeT::SizeT => {}
        TypeT::PtrdiffT => {}
        TypeT::Pointer(to, kind) => {
            scan_type(deps, &*to);
            match kind {
                PointerKind::Unknown => {}
                PointerKind::Ref => {}
                PointerKind::Array => {}
                PointerKind::ArrayPtr => {}
            }
        }
        TypeT::Unknown => {}
        TypeT::Error => {}
        TypeT::Void => {}
        TypeT::SLProp => {}
        TypeT::Bool => {}
        TypeT::TypeRef(n) => {
            deps.insert(match n {
                TypeRefKind::Typedef(n) => DeclName::Typedef(n.val.clone()),
                TypeRefKind::Struct(n) => DeclName::Struct(n.val.clone()),
                TypeRefKind::Union(n) => DeclName::Union(n.val.clone()),
            });
        }
        TypeT::Refine(ty, p) | TypeT::RefineAlways(ty, p) | TypeT::RefineUninit(ty, p) => {
            scan_type(deps, ty);
            scan_expr(deps, p);
        }
        TypeT::RefineValue(ty, _binding_name, binding_ty, p) => {
            scan_type(deps, ty);
            scan_type(deps, binding_ty);
            scan_expr(deps, p);
        }
        TypeT::Plain(ty) => scan_type(deps, ty),
        TypeT::SpecInt | TypeT::SpecNat => {}
    }
}

fn scan_inline_pulse_code(deps: &mut HashSet<DeclName>, code: &InlinePulseCode) {
    for tok in &code.tokens {
        match tok {
            InlinePulseToken::RValueAntiquot { expr, .. }
            | InlinePulseToken::LValueAntiquot { expr, .. } => scan_expr(deps, expr),
            InlinePulseToken::TypeAntiquot { ty, .. } | InlinePulseToken::Declare { ty, .. } => {
                scan_type(deps, ty)
            }
            InlinePulseToken::Verbatim(_) => {}
            InlinePulseToken::FieldAntiquot { ty, .. } => {
                scan_type(deps, ty);
            }
            InlinePulseToken::AuxFnAntiquot { ty, .. } => {
                scan_type(deps, ty);
            }
        }
    }
}

fn scan_expr(deps: &mut HashSet<DeclName>, rv: &Expr) {
    match &rv.val {
        ExprT::Var(_) => {}
        ExprT::Deref(v) => scan_expr(deps, v),
        ExprT::Member(x, _a) => scan_expr(deps, x),
        ExprT::VAttr(_, x) => scan_expr(deps, x),
        ExprT::Index(arr, idx) => {
            scan_expr(deps, arr);
            scan_expr(deps, idx);
        }
        ExprT::IntLit(_, ty) => scan_type(deps, ty),
        ExprT::Ref(v) => scan_expr(deps, v),
        ExprT::Cast(val, ty) => {
            scan_expr(deps, val);
            scan_type(deps, ty);
        }
        ExprT::Error(ty) => scan_type(deps, ty),
        ExprT::Malloc(ty) | ExprT::Calloc(ty) => scan_type(deps, ty),
        ExprT::MallocArray(ty, count) | ExprT::CallocArray(ty, count) => {
            scan_type(deps, ty);
            scan_expr(deps, count);
        }
        ExprT::Free(val) => scan_expr(deps, val),
        ExprT::PreIncr(val) | ExprT::PostIncr(val) | ExprT::PreDecr(val) | ExprT::PostDecr(val) => {
            scan_expr(deps, val)
        }
        ExprT::InlinePulse(code, ty) => {
            scan_type(deps, ty);
            scan_inline_pulse_code(deps, code);
        }
        ExprT::UnOp(_, arg) => scan_expr(deps, arg),
        ExprT::BinOp(_, lhs, rhs) => {
            scan_expr(deps, lhs);
            scan_expr(deps, rhs);
        }
        ExprT::FnCall(f, args) => {
            deps.insert(DeclName::Fn(f.val.clone()));
            scan_exprs(deps, args);
        }
        ExprT::BoolLit(_) => {}
        ExprT::Live(v) => scan_expr(deps, v),
        ExprT::Old(v) => scan_expr(deps, v),
        ExprT::Forall(_, ty, body) | ExprT::Exists(_, ty, body) => {
            scan_type(deps, ty);
            scan_expr(deps, body);
        }
        ExprT::StructInit(name, fields) => {
            deps.insert(DeclName::Struct(name.val.clone()));
            for (_fld_name, fld_val) in fields {
                scan_expr(deps, fld_val);
            }
        }
        ExprT::UnionInit(name, _, fld_val) => {
            deps.insert(DeclName::Union(name.val.clone()));
            scan_expr(deps, fld_val);
        }
        ExprT::Cond(cond, then_expr, else_expr) => {
            scan_expr(deps, cond);
            scan_expr(deps, then_expr);
            scan_expr(deps, else_expr);
        }
        ExprT::AssignExpr(lhs, rhs) => {
            scan_expr(deps, lhs);
            scan_expr(deps, rhs);
        }
    }
}

fn scan_exprs(deps: &mut HashSet<DeclName>, rvs: &Exprs) {
    for rv in rvs {
        scan_expr(deps, rv);
    }
}

fn scan_stmt(deps: &mut HashSet<DeclName>, stmt: &Stmt) {
    match &stmt.val {
        StmtT::Call(v) => scan_expr(deps, v),
        StmtT::Decl(_name, ty) => scan_type(deps, ty),
        StmtT::DeclStackArray {
            elem_type, size, ..
        } => {
            scan_type(deps, elem_type);
            scan_expr(deps, size);
        }
        StmtT::Assign(lhs, v) => {
            scan_expr(deps, lhs);
            scan_expr(deps, v);
        }
        StmtT::If(c, b1, b2) => {
            scan_expr(deps, c);
            scan_stmts(deps, b1);
            scan_stmts(deps, b2)
        }
        StmtT::While {
            cond,
            inv,
            requires,
            ensures,
            body,
        } => {
            scan_expr(deps, cond);
            scan_exprs(deps, inv);
            scan_exprs(deps, requires);
            scan_exprs(deps, ensures);
            scan_stmts(deps, body);
        }
        StmtT::Break | StmtT::Continue => {}
        StmtT::Return(v) => {
            if let Some(v) = v {
                scan_expr(deps, v)
            }
        }
        StmtT::Assert(v) => scan_expr(deps, v),
        StmtT::GhostStmt(code) => scan_inline_pulse_code(deps, code),
        StmtT::Goto(_) => {}
        StmtT::Label { ensures, .. } => {
            for e in &**ensures {
                scan_expr(deps, e)
            }
        }
        StmtT::GotoBlock {
            body,
            label: _,
            ensures,
        } => {
            scan_stmts(deps, body);
            for e in &**ensures {
                scan_expr(deps, e)
            }
        }
        StmtT::Error => {}
    }
}

fn scan_stmts(deps: &mut HashSet<DeclName>, stmts: &Vec<Rc<Stmt>>) {
    for stmt in stmts {
        scan_stmt(deps, stmt);
    }
}

fn decl_name(decl: &Decl) -> DeclName {
    match &decl.val {
        DeclT::FnDefn(fn_defn) => DeclName::Fn(fn_defn.decl.name.val.clone()),
        DeclT::FnDecl(fn_decl) => DeclName::Fn(fn_decl.name.val.clone()),
        DeclT::Typedef(type_defn) => DeclName::Typedef(type_defn.name.val.clone()),
        DeclT::StructDefn(struct_defn) => DeclName::Struct(struct_defn.name.val.clone()),
        DeclT::StructDecl(name) => DeclName::Struct(name.val.clone()),
        DeclT::UnionDefn(union_defn) => DeclName::Union(union_defn.name.val.clone()),
        DeclT::IncludeDecl(_) => DeclName::Include(decl.loc.clone()),
        DeclT::LetDecl(let_decl) => DeclName::Fn(let_decl.name.val.clone()),
        DeclT::OpaqueTypeDecl(decl) => DeclName::Typedef(decl.name.val.clone()),
        DeclT::GlobalVar(gv) => DeclName::GlobalVar(gv.name.val.clone()),
    }
}

fn scan_translation_unit(deps: &mut Deps<DeclName>, tu: &TranslationUnit) {
    fn scan_fn_decl(
        ds: &mut HashSet<DeclName>,
        FnDecl {
            name: _,
            ret_type,
            args,
            ghost_args,
            requires,
            ensures,
            is_pure: _,
            is_rec: _,
            decreases: _,
        }: &FnDecl,
    ) {
        for ga in ghost_args {
            scan_type(ds, &ga.ty);
        }
        for arg in args {
            scan_type(ds, &arg.ty)
        }
        scan_type(ds, &ret_type);

        for r in requires {
            scan_expr(ds, r);
        }
        for e in ensures {
            scan_expr(ds, e);
        }
    }

    for decl in &tu.decls {
        let n = decl_name(decl);
        match &decl.val {
            DeclT::FnDefn(FnDefn { decl, body }) => {
                let ds = deps.deps_for(n);
                scan_fn_decl(ds, &decl);
                scan_stmts(ds, &body);
            }
            DeclT::FnDecl(fn_decl) => {
                scan_fn_decl(deps.deps_for(n), fn_decl);
            }
            DeclT::Typedef(TypeDefn { name: _, body }) => scan_type(deps.deps_for(n), body),
            DeclT::StructDefn(StructDefn { name: _, fields }) => {
                let ds = deps.deps_for(n);
                for (_name, ty) in fields {
                    scan_type(ds, ty)
                }
            }
            DeclT::StructDecl(_) => {
                deps.deps_for(n);
            }
            DeclT::UnionDefn(UnionDefn { name: _, fields }) => {
                let ds = deps.deps_for(n);
                for (_name, ty) in fields {
                    scan_type(ds, ty)
                }
            }
            DeclT::IncludeDecl(code) => {
                let ds = deps.deps_for(n);
                scan_inline_pulse_code(ds, &code.code);
            }
            DeclT::LetDecl(let_decl) => {
                let ds = deps.deps_for(n);
                scan_type(ds, &let_decl.ret_type);
                for arg in &let_decl.params {
                    scan_type(ds, &arg.ty);
                }
                scan_exprs(ds, &let_decl.requires);
                scan_exprs(ds, &let_decl.ensures);
                scan_expr(ds, &let_decl.body);
            }
            DeclT::OpaqueTypeDecl(decl) => {
                let ds = deps.deps_for(n);
                scan_inline_pulse_code(ds, &decl.code);
            }
            DeclT::GlobalVar(GlobalVar {
                name: _,
                ty,
                init,
                is_pure: _,
            }) => {
                let ds = deps.deps_for(n);
                scan_type(ds, ty);
                if let Some(init) = init {
                    scan_expr(ds, init);
                }
            }
        }
    }
}

pub fn prune(tu: &mut TranslationUnit) {
    let mut deps = Deps::new();
    scan_translation_unit(&mut deps, tu);
    for decl in &tu.decls {
        if in_main_file(&tu.main_file_names, &decl.loc) {
            deps.add_root(decl_name(&decl))
        }
    }
    let deps = deps.propagate();
    tu.decls.retain(|decl| deps.contains(&decl_name(decl)));
}
