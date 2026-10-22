//! Preserve C entity identity before name-based dependency and merge passes.
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    diag::{Diagnostic, DiagnosticLevel, Diagnostics},
    ir::*,
};

#[derive(Default)]
pub struct UnitSymbols {
    pub identity: UnitIdentity,
    pub context: String,
    pub symbols: Vec<CSymbol>,
}

pub struct CSymbol {
    pub name: Rc<str>,
    pub kind: u32,
    pub signature: String,
    pub internal: bool,
    pub definition: bool,
    pub inline: bool,
    pub loc: Rc<SourceInfo>,
}

pub struct HeaderStatic {
    name: Rc<str>,
    context: String,
    signature: String,
    loc: Rc<SourceInfo>,
}

pub fn header_statics(units: &[(TranslationUnit, UnitSymbols)]) -> Vec<HeaderStatic> {
    if units.len() < 2 {
        return Vec::new();
    }
    units
        .iter()
        .flat_map(|(tu, symbols)| {
            symbols.symbols.iter().filter_map(|symbol| {
                (symbol.kind == 0
                    && symbol.internal
                    && symbol.definition
                    && !tu
                        .main_file_names
                        .contains(&symbol.loc.location().file_name))
                .then(|| HeaderStatic {
                    name: Rc::from(format!("{}{}", symbols.identity.prefix, symbol.name)),
                    context: symbols.context.clone(),
                    signature: symbol.signature.clone(),
                    loc: symbol.loc.clone(),
                })
            })
        })
        .collect()
}

/// Compare after elaboration, retaining all dependency names. In particular,
/// otherwise identical references to different TU-local entities must not match.
pub fn shared_header_proofs(
    tu: &TranslationUnit,
    candidates: &[HeaderStatic],
    addr_taken: &HashSet<Rc<str>>,
) -> HashMap<Rc<str>, Rc<str>> {
    let definitions: HashMap<_, _> = tu
        .decls
        .iter()
        .filter_map(|decl| match &decl.val {
            DeclT::FnDefn(defn) => Some((defn.decl.name.val.clone(), defn)),
            _ => None,
        })
        .collect();
    let mut candidates: Vec<_> = candidates.iter().collect();
    candidates.sort_by(|a, b| a.name.cmp(&b.name));
    let mut representatives = HashMap::new();
    let mut shared = HashMap::new();
    for candidate in candidates {
        let Some(defn) = definitions.get(&candidate.name) else {
            continue;
        };
        if defn.decl.is_rec || addr_taken.contains(&candidate.name) {
            continue;
        }
        let mut normalized = (*defn).clone();
        Rc::make_mut(&mut normalized.decl.name).val = Rc::from("");
        let key = (
            &candidate.context,
            &candidate.signature,
            &candidate.loc,
            normalized,
        );
        if let Some(representative) = representatives.get(&key) {
            shared.insert(candidate.name.clone(), Rc::clone(representative));
        } else {
            representatives.insert(key, candidate.name.clone());
        }
    }
    shared
}

fn error(diags: &mut Diagnostics, loc: &SourceInfo, message: impl Into<String>) {
    diags.report(Diagnostic {
        loc: loc.location().clone(),
        level: DiagnosticLevel::Error,
        msg: message.into(),
    });
}

#[derive(Clone, Default)]
pub struct UnitIdentity {
    pub logical_path: String,
    pub prefix: String,
}

fn prefix(path: &str) -> String {
    // Hash a logical path, never contents: identical files are distinct TUs.
    let mut hash = 0xcbf29ce484222325u64;
    for byte in path.bytes() {
        hash = (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3);
    }
    format!("__pal_tu_{hash:016x}_")
}

pub fn identities(files: &[String]) -> Result<Vec<UnitIdentity>, String> {
    if files.len() < 2 {
        return Ok(vec![UnitIdentity::default(); files.len()]);
    }
    let paths = files
        .iter()
        .map(|file| {
            std::fs::canonicalize(file)
                .map_err(|e| format!("cannot establish translation-unit identity for {file}: {e}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut root = paths[0].parent().ok_or("input has no parent directory")?;
    for path in &paths {
        while !path.parent().is_some_and(|p| p.starts_with(root)) {
            root = root
                .parent()
                .ok_or("inputs have no common source ancestor")?;
        }
    }
    let mut canonical = HashSet::new();
    let mut hashes = HashMap::new();
    let mut result = Vec::new();
    for path in &paths {
        if !canonical.insert(path) {
            return Err(format!(
                "duplicate selected translation unit: {}",
                path.display()
            ));
        }
        let logical_path = path
            .strip_prefix(root)
            .unwrap()
            .components()
            .map(|c| {
                c.as_os_str()
                    .to_str()
                    .ok_or("non-UTF-8 translation-unit path")
            })
            .collect::<Result<Vec<_>, _>>()?
            .join("/");
        let prefix = prefix(&logical_path);
        if hashes
            .insert(prefix.clone(), logical_path.clone())
            .is_some()
        {
            return Err("translation-unit identity hash collision".into());
        }
        result.push(UnitIdentity {
            logical_path,
            prefix,
        });
    }
    Ok(result)
}

fn compatible_signature(a: &CSymbol, b: &CSymbol) -> bool {
    if a.kind != b.kind {
        return false;
    }
    if a.signature == b.signature {
        return true;
    }
    // Complete a one-dimensional external object array, never a nested
    // declarator or a function signature.
    if a.kind == 1 {
        for (incomplete, complete) in [(&a.signature, &b.signature), (&b.signature, &a.signature)] {
            if let Some(element) = incomplete.strip_suffix("[]")
                && !element.contains(['(', '['])
                && let Some(size) = complete.strip_prefix(element)
                && let Some(size) = size.strip_prefix('[').and_then(|s| s.strip_suffix(']'))
                && !size.is_empty()
                && size.bytes().all(|c| c.is_ascii_digit())
            {
                return true;
            }
        }
    }
    false
}

fn normalize_type(
    ty: &Rc<Type>,
    aliases: &HashMap<Rc<str>, Rc<Type>>,
    seen: &mut Bound,
) -> Rc<Type> {
    if let TypeT::TypeRef(TypeRefKind::Typedef(name)) = &ty.val
        && let Some(body) = aliases.get(&name.val)
        && seen.insert(name.val.clone())
    {
        let result = normalize_type(body, aliases, seen);
        seen.remove(&name.val);
        return result;
    }
    let mut result = ty.clone();
    match &mut Rc::make_mut(&mut result).val {
        TypeT::Pointer(t, _)
        | TypeT::FixedArray(t, _)
        | TypeT::FlexArray(t)
        | TypeT::Plain(t)
        | TypeT::Nullable(t)
        | TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _) => {
            *t = normalize_type(t, aliases, seen);
        }
        TypeT::RefineValue(t, _, binding, _) => {
            *t = normalize_type(t, aliases, seen);
            *binding = normalize_type(binding, aliases, seen);
        }
        TypeT::FnPtr { args, ret } => {
            for arg in args {
                *arg = normalize_type(arg, aliases, seen);
            }
            *ret = normalize_type(ret, aliases, seen);
        }
        _ => {}
    }
    result
}

pub fn prepare(units: &mut [(TranslationUnit, UnitSymbols)], diags: &mut Diagnostics) {
    let multiple = units.len() > 1;
    let mut entities: HashMap<(u32, Rc<str>), Vec<(usize, &CSymbol, &str)>> = HashMap::new();
    for (index, (_, symbols)) in units.iter().enumerate() {
        if multiple {
            debug_assert_eq!(
                symbols.identity.prefix,
                prefix(&symbols.identity.logical_path)
            );
        }
        for symbol in &symbols.symbols {
            if symbol.name.starts_with("__pal_tu_") {
                error(
                    diags,
                    &symbol.loc,
                    "reserved translation-unit identity prefix",
                );
            }
            if symbol.internal {
                continue;
            }
            // Functions and objects share the C linker namespace.
            let kind = if symbol.kind <= 1 || symbol.kind == 5 {
                0
            } else {
                symbol.kind
            };
            let key = (kind, symbol.name.clone());
            let previous_symbols = entities.entry(key).or_default();
            for (previous_unit, previous, context) in previous_symbols.iter() {
                if *previous_unit != index {
                    if !compatible_signature(previous, symbol) {
                        error(
                            diags,
                            &symbol.loc,
                            format!("incompatible C declarations for {}", symbol.name),
                        );
                    }
                    if symbol.kind <= 1 && *context != symbols.context {
                        error(
                            diags,
                            &symbol.loc,
                            format!("incompatible compilation contexts for {}", symbol.name),
                        );
                    }
                    if symbol.definition
                        && previous.definition
                        && !(symbol.kind == 0
                            && symbol.inline
                            && previous.inline
                            && symbol.loc == previous.loc)
                    {
                        error(
                            diags,
                            &symbol.loc,
                            format!("conflicting external definitions of {}", symbol.name),
                        );
                    }
                }
            }
            previous_symbols.push((index, symbol, &symbols.context));
        }
    }
    for (tu, symbols) in units.iter_mut() {
        if multiple {
            let prefix = &symbols.identity.prefix;
            let names: HashMap<_, _> = symbols
                .symbols
                .iter()
                .filter(|s| s.internal)
                .map(|s| {
                    (
                        s.name.clone(),
                        Rc::<str>::from(format!("{prefix}{}", s.name)),
                    )
                })
                .collect();
            let mut renamer = Renamer {
                names: &names,
                diags,
                raw_reference: false,
                shadowed: Bound::new(),
                shadow_reference: false,
                in_pulse: false,
            };
            for decl in &mut tu.decls {
                renamer.decl(decl);
            }
        }
    }
    // Named type/Pulse definitions cannot safely be chosen by input order.
    // Equal copies from common headers are harmless; differing representations
    // or annotations require a separately supported representation.
    let mut definitions = HashMap::new();
    let mut globals: HashMap<Rc<str>, Vec<(usize, Rc<Type>, &GlobalVar)>> = HashMap::new();
    let mut incompatible_globals = HashSet::new();
    for (index, (tu, _)) in units.iter().enumerate() {
        let aliases = tu
            .decls
            .iter()
            .filter_map(|d| match &d.val {
                DeclT::Typedef(d) if !d.is_pointer_view => {
                    Some((d.name.val.clone(), d.body.clone()))
                }
                _ => None,
            })
            .collect();
        for decl in &tu.decls {
            if let DeclT::GlobalVar(global) = &decl.val {
                let ty = normalize_type(&global.ty, &aliases, &mut Bound::new());
                let previous = globals.entry(global.name.val.clone()).or_default();
                for (unit, old_ty, old) in previous.iter() {
                    let array_compatible = match (&old_ty.val, &ty.val) {
                        (TypeT::FlexArray(a), TypeT::FixedArray(b, _))
                        | (TypeT::FixedArray(a, _), TypeT::FlexArray(b))
                        | (TypeT::Pointer(a, PointerKind::Array), TypeT::FixedArray(b, _))
                        | (TypeT::FixedArray(a, _), TypeT::Pointer(b, PointerKind::Array)) => {
                            a == b
                        }
                        _ => false,
                    };
                    if *unit != index
                        && ((old_ty != &ty && !array_compatible)
                            || old.is_enum_constant != global.is_enum_constant)
                    {
                        incompatible_globals.insert(global.name.val.clone());
                        error(
                            diags,
                            &decl.loc,
                            format!(
                                "incompatible translated object declarations of {}",
                                global.name.val
                            ),
                        );
                    }
                }
                previous.push((index, ty, global));
            }
            let key = match &decl.val {
                DeclT::Typedef(d) => Some((0, d.name.val.clone())),
                DeclT::StructDefn(d) => Some((1, d.name.val.clone())),
                DeclT::UnionDefn(d) => Some((2, d.name.val.clone())),
                DeclT::FnDefn(d) => Some((3, d.decl.name.val.clone())),
                DeclT::IncludeDecl(d) => Some((4, d.module_name.clone())),
                DeclT::OpaqueTypeDecl(d) => Some((5, d.name.val.clone())),
                DeclT::LetDecl(d) => Some((6, d.name.val.clone())),
                _ => None,
            };
            if let Some(key) = key {
                if let Some((previous_unit, previous)) = definitions.get(&key) {
                    if (*previous_unit != index || key.0 <= 2) && *previous != &decl.val {
                        error(
                            diags,
                            &decl.loc,
                            format!("incompatible translated definitions of {}", key.1),
                        );
                    }
                } else {
                    definitions.insert(key, (index, &decl.val));
                }
            }
        }
    }
    // Retain an original type representation rather than erasing typedef
    // semantics before elaboration. Relative TU paths break equivalent ties.
    let canonical_globals: HashMap<_, _> = globals
        .iter()
        .filter_map(|(name, entries)| {
            let first_unit = entries[0].0;
            if incompatible_globals.contains(name)
                || entries.iter().all(|(unit, _, _)| *unit == first_unit)
            {
                return None;
            }
            let preferred = entries
                .iter()
                .min_by_key(|(unit, normalized, global)| {
                    (
                        !matches!(normalized.val, TypeT::FixedArray(_, _)),
                        global.init.is_none(),
                        global.is_extern,
                        &units[*unit].1.identity.logical_path,
                        global.ty.to_string(),
                    )
                })
                .unwrap();
            Some((name.clone(), preferred.2.ty.clone()))
        })
        .collect();
    for (tu, _) in units.iter_mut() {
        for decl in &mut tu.decls {
            if let DeclT::GlobalVar(global) = &mut decl.val
                && let Some(ty) = canonical_globals.get(&global.name.val)
            {
                global.ty = ty.clone();
            }
        }
    }
}

type Bound = HashSet<Rc<str>>;

struct Renamer<'a> {
    names: &'a HashMap<Rc<str>, Rc<str>>,
    diags: &'a mut Diagnostics,
    raw_reference: bool,
    shadowed: Bound,
    shadow_reference: bool,
    in_pulse: bool,
}

impl Renamer<'_> {
    fn bind(&mut self, scope: &mut Bound, name: &Ident) {
        if name.val.starts_with("__pal_tu_") {
            error(
                self.diags,
                &name.loc,
                "reserved translation-unit identity prefix in binding",
            );
        }
        scope.insert(name.val.clone());
    }

    fn name(&mut self, name: &mut Rc<Ident>, bound: &Bound) {
        if self.in_pulse && self.shadowed.contains(&name.val) {
            self.shadow_reference = true;
        }
        if !bound.contains(&name.val) {
            if let Some(replacement) = self.names.get(&name.val) {
                Rc::make_mut(name).val = replacement.clone();
            }
        }
    }

    fn ty(&mut self, ty: &mut Rc<Type>, bound: &Bound) {
        match &mut Rc::make_mut(ty).val {
            TypeT::Pointer(t, _)
            | TypeT::FixedArray(t, _)
            | TypeT::FlexArray(t)
            | TypeT::Plain(t)
            | TypeT::Nullable(t) => self.ty(t, bound),
            TypeT::FnPtr { args, ret } => {
                for a in args {
                    self.ty(a, bound);
                }
                self.ty(ret, bound);
            }
            TypeT::Refine(t, p) | TypeT::RefineAlways(t, p) | TypeT::RefineUninit(t, p) => {
                self.ty(t, bound);
                self.expr(p, bound);
            }
            TypeT::RefineValue(t, name, binding, p) => {
                self.ty(t, bound);
                self.ty(binding, bound);
                let mut nested = bound.clone();
                self.bind(&mut nested, name);
                self.expr(p, &nested);
            }
            TypeT::Void
            | TypeT::Bool
            | TypeT::Int { .. }
            | TypeT::Float { .. }
            | TypeT::SizeT
            | TypeT::PtrdiffT
            | TypeT::SpecInt
            | TypeT::SpecNat
            | TypeT::SLProp
            | TypeT::TypeRef(_)
            | TypeT::Unknown
            | TypeT::Error => {}
        }
    }

    fn pulse(&mut self, code: &mut InlinePulseCode, bound: &Bound) -> Bound {
        let previous = self.in_pulse;
        self.in_pulse = true;
        let mut scope = bound.clone();
        for token in &mut code.tokens {
            match token {
                InlinePulseToken::RValueAntiquot { expr, .. }
                | InlinePulseToken::LValueAntiquot { expr, .. } => self.expr(expr, &scope),
                InlinePulseToken::TypeAntiquot { ty, .. }
                | InlinePulseToken::FieldAntiquot { ty, .. }
                | InlinePulseToken::AuxFnAntiquot { ty, .. } => self.ty(ty, &scope),
                InlinePulseToken::Declare { ident, ty, .. } => {
                    self.ty(ty, &scope);
                    self.bind(&mut scope, ident);
                }
                InlinePulseToken::Verbatim(text) => {
                    // Raw F* module names are not C references. Do not silently
                    // bind an old unqualified module to another TU's entity.
                    for name in self.names.keys() {
                        if text.text.val.as_ref() == format!("Func_{name}")
                            || text.text.val.as_ref() == format!("Global_{name}")
                            || text.text.val.as_ref() == format!("Funcptr_{name}")
                        {
                            // Verbatim fragments do not carry a C source range;
                            // the containing declaration is diagnosed below.
                            self.raw_reference = true;
                        }
                    }
                }
            }
        }
        self.in_pulse = previous;
        scope
    }

    fn exprs(&mut self, exprs: &mut Exprs, bound: &Bound) {
        for e in exprs {
            self.expr(e, bound);
        }
    }

    fn expr(&mut self, expr: &mut Rc<Expr>, bound: &Bound) {
        match &mut Rc::make_mut(expr).val {
            ExprT::Var(n) | ExprT::FnRef(n) => self.name(n, bound),
            ExprT::FnCall(n, args) => {
                self.name(n, bound);
                self.exprs(args, bound);
            }
            ExprT::FnPtrCall(f, args) => {
                self.expr(f, bound);
                self.exprs(args, bound);
            }
            ExprT::IntLit(_, t)
            | ExprT::FloatLit(_, t)
            | ExprT::Malloc(t)
            | ExprT::Calloc(t)
            | ExprT::SizeOf(t)
            | ExprT::AlignOf(t)
            | ExprT::Error(t) => self.ty(t, bound),
            ExprT::InlinePulse(code, t) => {
                self.pulse(Rc::make_mut(code), bound);
                self.ty(t, bound);
            }
            ExprT::Cast(e, t)
            | ExprT::MallocArray(t, e)
            | ExprT::CallocArray(t, e)
            | ExprT::MallocFlex(t, e)
            | ExprT::CallocFlex(t, e)
            | ExprT::MemsetZero(t, e)
            | ExprT::ContainerOf(e, t, _) => {
                self.expr(e, bound);
                self.ty(t, bound);
            }
            ExprT::Forall(n, t, e) | ExprT::Exists(n, t, e) => {
                self.ty(t, bound);
                let mut nested = bound.clone();
                self.bind(&mut nested, n);
                self.expr(e, &nested);
            }
            ExprT::ArrayInit { elem_ty, elems, .. } => {
                self.ty(elem_ty, bound);
                self.exprs(elems, bound);
            }
            ExprT::Memset(t, a, b, c) => {
                self.ty(t, bound);
                self.expr(a, bound);
                self.expr(b, bound);
                self.expr(c, bound);
            }
            ExprT::Deref(e)
            | ExprT::Member(e, _)
            | ExprT::VAttr(_, e)
            | ExprT::Ref(e)
            | ExprT::UnOp(_, e)
            | ExprT::Live(e)
            | ExprT::Old(e)
            | ExprT::Free(e)
            | ExprT::PreIncr(e)
            | ExprT::PostIncr(e)
            | ExprT::PreDecr(e)
            | ExprT::PostDecr(e)
            | ExprT::UnionInit(_, _, e) => self.expr(e, bound),
            ExprT::Index(a, b) | ExprT::BinOp(_, a, b) | ExprT::AssignExpr(a, b) => {
                self.expr(a, bound);
                self.expr(b, bound);
            }
            ExprT::Cond(a, b, c) => {
                self.expr(a, bound);
                self.expr(b, bound);
                self.expr(c, bound);
            }
            ExprT::StructInit(_, fields) => {
                for (_, e) in fields {
                    self.expr(e, bound);
                }
            }
            ExprT::BoolLit(_) => {}
        }
    }

    fn stmts(&mut self, stmts: &mut Stmts, outer: &Bound) {
        let mut scope = outer.clone();
        for stmt in stmts {
            match &mut Rc::make_mut(stmt).val {
                StmtT::Decl(n, t) => {
                    if self.names.contains_key(&n.val) {
                        self.shadowed.insert(n.val.clone());
                    }
                    self.ty(t, &scope);
                    self.bind(&mut scope, n);
                }
                StmtT::Let(n, t, e) => {
                    if self.names.contains_key(&n.val) {
                        self.shadowed.insert(n.val.clone());
                    }
                    self.ty(t, &scope);
                    // A C local's scope includes its initializer.
                    self.bind(&mut scope, n);
                    self.expr(e, &scope);
                }
                StmtT::DeclStackArray {
                    name,
                    elem_type,
                    size,
                } => {
                    if self.names.contains_key(&name.val) {
                        self.shadowed.insert(name.val.clone());
                    }
                    self.ty(elem_type, &scope);
                    self.expr(size, &scope);
                    self.bind(&mut scope, name);
                }
                StmtT::Call(e) | StmtT::Assert(e) | StmtT::Return(Some(e)) => self.expr(e, &scope),
                StmtT::Assign(a, b) => {
                    self.expr(a, &scope);
                    self.expr(b, &scope);
                }
                StmtT::If {
                    cond,
                    then_branch,
                    else_branch,
                    ensures,
                } => {
                    self.expr(cond, &scope);
                    self.exprs(Rc::make_mut(ensures), &scope);
                    self.stmts(Rc::make_mut(then_branch), &scope);
                    self.stmts(Rc::make_mut(else_branch), &scope);
                }
                StmtT::While {
                    cond,
                    inv,
                    requires,
                    ensures,
                    body,
                } => {
                    self.expr(cond, &scope);
                    self.exprs(Rc::make_mut(inv), &scope);
                    self.exprs(Rc::make_mut(requires), &scope);
                    self.exprs(Rc::make_mut(ensures), &scope);
                    self.stmts(Rc::make_mut(body), &scope);
                }
                StmtT::Match {
                    scrutinee,
                    branches,
                    default_branch,
                    ensures,
                } => {
                    self.expr(scrutinee, &scope);
                    self.exprs(Rc::make_mut(ensures), &scope);
                    for branch in Rc::make_mut(branches) {
                        let branch = Rc::make_mut(branch);
                        self.exprs(Rc::make_mut(&mut branch.patterns), &scope);
                        self.stmts(Rc::make_mut(&mut branch.body), &scope);
                    }
                    self.stmts(Rc::make_mut(default_branch), &scope);
                }
                StmtT::GhostStmt(code) => {
                    scope = self.pulse(Rc::make_mut(code), &scope);
                }
                StmtT::Label { ensures, .. } => self.exprs(Rc::make_mut(ensures), &scope),
                StmtT::GotoBlock { body, ensures, .. } => {
                    self.exprs(Rc::make_mut(ensures), &scope);
                    self.stmts(Rc::make_mut(body), &scope);
                }
                StmtT::Break
                | StmtT::Continue
                | StmtT::Return(None)
                | StmtT::Goto(_)
                | StmtT::Error => {}
            }
        }
    }

    fn function(&mut self, d: &mut FnDecl) -> Bound {
        let mut scope = Bound::new();
        self.name(&mut d.name, &scope);
        for arg in &d.args {
            if let Some(n) = &arg.name {
                self.bind(&mut scope, n);
            }
        }
        for arg in &d.ghost_args {
            self.bind(&mut scope, &arg.name);
        }
        self.ty(&mut d.ret_type, &scope);
        for arg in &mut d.args {
            self.ty(&mut arg.ty, &scope);
        }
        for arg in &mut d.ghost_args {
            self.ty(&mut arg.ty, &scope);
        }
        self.exprs(&mut d.requires, &scope);
        self.exprs(&mut d.ensures, &scope);
        if let Some(e) = &mut d.decreases {
            self.expr(e, &scope);
        }
        scope
    }

    fn decl(&mut self, decl: &mut Decl) {
        self.shadowed.clear();
        let scope = Bound::new();
        match &mut decl.val {
            DeclT::FnDefn(d) => {
                let scope = self.function(&mut d.decl);
                self.stmts(&mut d.body, &scope);
            }
            DeclT::FnDecl(d) => {
                self.function(d);
            }
            DeclT::GlobalVar(d) => {
                self.name(&mut d.name, &scope);
                self.ty(&mut d.ty, &scope);
                if let Some(e) = &mut d.init {
                    self.expr(e, &scope);
                }
            }
            DeclT::Typedef(d) => self.ty(&mut d.body, &scope),
            DeclT::StructDefn(d) => {
                self.ty(&mut d.refines, &scope);
                for f in &mut d.fields {
                    match &mut f.val {
                        FieldT::Plain { ty, .. } | FieldT::BitField { ty, .. } => {
                            self.ty(ty, &scope)
                        }
                    }
                }
            }
            DeclT::UnionDefn(d) => {
                for f in &mut d.fields {
                    match &mut f.val {
                        FieldT::Plain { ty, .. } | FieldT::BitField { ty, .. } => {
                            self.ty(ty, &scope)
                        }
                    }
                }
            }
            DeclT::IncludeDecl(d) => {
                self.pulse(&mut d.code, &scope);
            }
            DeclT::OpaqueTypeDecl(d) => {
                self.pulse(&mut d.code, &scope);
            }
            DeclT::LetDecl(d) => {
                let mut scope = scope;
                for arg in &d.params {
                    if let Some(n) = &arg.name {
                        self.bind(&mut scope, n);
                    }
                }
                self.ty(&mut d.ret_type, &scope);
                for arg in &mut d.params {
                    self.ty(&mut arg.ty, &scope);
                }
                self.exprs(&mut d.requires, &scope);
                self.exprs(&mut d.ensures, &scope);
                self.expr(&mut d.body, &scope);
            }
            DeclT::StructDecl(_) => {}
        }
        if self.raw_reference {
            error(
                self.diags,
                &decl.loc,
                "raw Pulse reference to a TU-local C entity; use a C antiquotation",
            );
            self.raw_reference = false;
        }
        if self.shadow_reference {
            error(
                self.diags,
                &decl.loc,
                "shadowed TU-local name in C antiquotation is unsupported after block flattening",
            );
            self.shadow_reference = false;
        }
    }
}
