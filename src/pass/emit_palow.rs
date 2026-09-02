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

use std::collections::HashMap;
use std::rc::Rc;

use crate::ir::*;

/// C code names its scalars through typedefs (`uint32_t`, `my_len_t`, ...), so
/// without unfolding them almost nothing in the test suite would be
/// translatable. Struct and union typedefs are left folded; they are milestone
/// 4's problem, and unfolding them here would only change the wording of the
/// skip message.
struct Typedefs<'a>(HashMap<&'a str, &'a Rc<Type>>);

impl<'a> Typedefs<'a> {
    fn new(tu: &'a TranslationUnit) -> Self {
        let mut m = HashMap::new();
        for decl in &tu.decls {
            if let DeclT::Typedef(td) = &decl.val {
                m.insert(&*td.name.val, &td.body);
            }
        }
        Typedefs(m)
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
                TypeT::TypeRef(TypeRefKind::Typedef(n)) => match self.0.get(&*n.val) {
                    Some(body) => ty = body,
                    None => return ty,
                },
                _ => return ty,
            }
        }
        ty
    }
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
fn palow_name(tds: &Typedefs, ty: &Type) -> Option<String> {
    match &tds.resolve(ty).val {
        TypeT::Bool => Some("bool_t".to_string()),
        TypeT::Int { signed, width } => {
            Some(format!("{}int{}_t", if *signed { "" } else { "u" }, width))
        }
        TypeT::SizeT => Some("size_t".to_string()),
        // Every pointer kind is the same type here; that is the point.
        TypeT::Pointer(..) => Some("ptr".to_string()),
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
        TypeT::Pointer(..) => Some("ptr".to_string()),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => fstar_type(tds, t),
        _ => None,
    }
}

/// The pointee of a pointer parameter, skipping the wrappers that do not
/// change the representation.
fn pointee<'a>(tds: &'a Typedefs, ty: &'a Type) -> Option<&'a Rc<Type>> {
    match &tds.resolve(ty).val {
        TypeT::Pointer(to, _) => Some(to),
        TypeT::Refine(t, _)
        | TypeT::RefineAlways(t, _)
        | TypeT::RefineUninit(t, _)
        | TypeT::RefineValue(t, ..)
        | TypeT::Plain(t)
        | TypeT::Nullable(t) => pointee(tds, t),
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
}

/// Build the Pulse declaration for one C function, or explain why we cannot.
fn emit_fn(tds: &Typedefs, decl: &FnDecl) -> Result<FnSurface, String> {
    let name = format!("func_{}", decl.name.val);

    let mut params: Vec<String> = Vec::new();
    let mut ghosts: Vec<String> = Vec::new();
    let mut perms: Vec<String> = Vec::new();
    // (points-to slprop, whether it is preserved unchanged)
    let mut owned: Vec<(String, bool)> = Vec::new();
    // For ownership returned with a possibly-changed value: the value binder
    // name, its type, and the points-to applied to everything but the value.
    let mut fresh: Vec<(String, String, String)> = Vec::new();

    for (i, arg) in decl.args.iter().enumerate() {
        let pname = match &arg.name {
            Some(n) => format!("var_{}", n.val),
            None => format!("arg_{}", i),
        };
        let fty = fstar_type(tds, &arg.ty)
            .ok_or_else(|| format!("parameter {} is {}", pname, describe(tds.resolve(&arg.ty))))?;
        params.push(format!("({}: {})", pname, fty));

        if let Some(pt) = pointee(tds, &arg.ty) {
            // `void *` and pointers to aggregates are not modelled yet.
            let pn = palow_name(tds, pt).ok_or_else(|| {
                format!(
                    "parameter {} points to {}",
                    pname,
                    describe(tds.resolve(pt))
                )
            })?;
            let vty = fstar_type(tds, pt).unwrap();
            let vname = format!("val_{}", pname.trim_start_matches("var_"));
            ghosts.push(format!("(#{}: erased {})", vname, vty));
            let shared = is_shared(arg.mode);
            let perm = if shared {
                let p = format!("perm_{}", pname.trim_start_matches("var_"));
                perms.push(format!("(#{}: perm)", p));
                p
            } else {
                "1.0R".to_string()
            };
            owned.push((
                format!("{}_pts_to {} {} {}", pn, pname, perm, vname),
                shared,
            ));
            if !shared {
                fresh.push((
                    format!("{}'", vname),
                    vty,
                    format!("{}_pts_to {} 1.0R", pn, pname),
                ));
            }
        }
    }

    let ret = fstar_type(tds, &decl.ret_type)
        .ok_or_else(|| format!("it returns {}", describe(tds.resolve(&decl.ret_type))))?;

    let mut out = String::new();
    out += &format!("fn {}", name);
    if params.is_empty() && perms.is_empty() && ghosts.is_empty() {
        // Pulse has no nullary `fn`; `f(void)` becomes `f ()`.
        out += " ()";
    }
    for p in &params {
        out += &format!(" {}", p);
    }
    for g in &perms {
        out += &format!(" {}", g);
    }
    for g in &ghosts {
        out += &format!(" {}", g);
    }
    out += "\n";

    // Ownership that the function gives back unchanged is `preserves`; the rest
    // is a `requires`/`ensures` pair, with the postcondition existentially
    // quantified because we are not translating the user's contract yet.
    let mut req: Vec<String> = Vec::new();
    for (slprop, shared) in &owned {
        if *shared {
            out += &format!("  preserves {}\n", slprop);
        } else {
            req.push(slprop.clone());
        }
    }
    if req.is_empty() {
        out += "  requires emp\n";
    } else {
        out += &format!("  requires {}\n", req.join(" **\n           "));
    }
    out += &format!("  returns  ret_{} : {}\n", decl.name.val, ret);
    if fresh.is_empty() {
        out += "  ensures  emp\n";
    } else {
        let binders: Vec<String> = fresh
            .iter()
            .map(|(b, t, _)| format!("({}: {})", b, t))
            .collect();
        let bodies: Vec<String> = fresh
            .iter()
            .map(|(b, _, s)| format!("{} {}", s, b))
            .collect();
        out += &format!(
            "  ensures  exists* {}.\n             {}\n",
            binders.join(" "),
            bodies.join(" **\n             ")
        );
    }

    Ok(FnSurface { decl: out })
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

pub fn emit_palow(tu: &TranslationUnit) -> Vec<PalowModule> {
    let tds = Typedefs::new(tu);
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
    code += "open Pulse.Lib.C.Palow.Machine\n\n";
    for m in ["Int8", "Int16", "Int32", "Int64"] {
        code += &format!("module {} = FStar.{}\n", m, m);
    }
    for m in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        code += &format!("module {} = FStar.{}\n", m, m);
    }
    code += "module SizeT = FStar.SizeT\n\n";

    for decl in &tu.decls {
        let (fndecl, defn) = match &decl.val {
            DeclT::FnDefn(d) => (&d.decl, Some(d)),
            DeclT::FnDecl(d) => (d, None),
            _ => continue,
        };
        let sig = match emit_fn(&tds, fndecl) {
            Ok(s) => s,
            Err(why) => {
                code += &format!("(* skipped {}: {} *)\n\n", fndecl.name.val, why);
                continue;
            }
        };

        let body = match defn {
            None => Err("it has no definition here".to_string()),
            Some(d) => {
                let mut env = base.clone();
                env.push_fn_decl_args_for_body(fndecl);
                emit_body(&tds, env, d)
            }
        };
        code += &sig.decl;
        match body {
            Ok(lines) => {
                code += "{\n";
                for l in &lines {
                    code += &format!("  {}\n", l);
                }
                code += "}\n\n";
            }
            Err(why) => {
                code += &format!("{{\n  admit() (* body: {} *)\n}}\n\n", why);
            }
        }
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
struct Slot {
    name: String,
    palow_ty: String,
    init: bool,
}

struct Body<'a> {
    tds: &'a Typedefs<'a>,
    env: Env,
    lines: Vec<String>,
    /// C locals with a stack slot, in allocation order.
    slots: Vec<Slot>,
    tmp: usize,
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

    /// The address of an lvalue, as an F* expression of type `ptr`.
    fn addr(&mut self, e: &Expr) -> Result<String, String> {
        match &e.val {
            ExprT::Var(v) => {
                if self.slots.iter().any(|s| s.name == *v.val) {
                    Ok(format!("loc_{}", v.val))
                } else {
                    // A parameter of scalar type has no address in the Palow
                    // model unless the C code takes one, in which case the
                    // translation would have to give it a slot too.
                    Err(format!("`{}` has no address", v.val))
                }
            }
            ExprT::Deref(inner) => self.rvalue(inner),
            ExprT::VAttr(_, inner) => self.addr(inner),
            _ => Err("unsupported lvalue".to_string()),
        }
    }

    /// An rvalue, as an F* expression. Reads are effectful, so they are bound
    /// to a fresh name and the binding is pushed onto `lines`.
    fn rvalue(&mut self, e: &Expr) -> Result<String, String> {
        match &e.val {
            ExprT::VAttr(_, inner) => self.rvalue(inner),
            ExprT::Var(v) => {
                if let Some(s) = self.slots.iter().find(|s| s.name == *v.val) {
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
                } else {
                    // A global: it has storage, and translating it means
                    // deciding who owns it. Milestone 2 does not cover that.
                    Err(format!("`{}` is a global", v.val))
                }
            }
            ExprT::Deref(_) => {
                let ty = self.ty_of(e)?;
                let pn = palow_name(self.tds, &ty)
                    .ok_or_else(|| format!("a dereference yields {}", describe(&ty)))?;
                let a = self.addr(e)?;
                let t = self.fresh("deref");
                self.lines.push(format!("let {} = {}_read {};", t, pn, a));
                Ok(t)
            }
            ExprT::BoolLit(b) => Ok(if *b { "true" } else { "false" }.to_string()),
            ExprT::IntLit(n, ty) => int_literal(self.tds, n, ty),
            ExprT::Cast(inner, to) => {
                let from = self.ty_of(inner)?;
                if fstar_type(self.tds, &from) == fstar_type(self.tds, to) {
                    return self.rvalue(inner);
                }
                let v = self.rvalue(inner)?;
                convert(self.tds.resolve(&from), self.tds.resolve(to), &v)
            }
            ExprT::BinOp(op, l, r) => {
                let ty = self.ty_of(l)?;
                let opstr = binop(self.tds, *op, &ty)?;
                let a = self.rvalue(l)?;
                let b = self.rvalue(r)?;
                Ok(format!("({} {} {})", a, opstr, b))
            }
            ExprT::UnOp(UnOp::Not, inner) => {
                let a = self.rvalue(inner)?;
                Ok(format!("(not {})", a))
            }
            _ => Err(format!("{} is not translated yet", expr_kind(e))),
        }
    }

    fn alloc_slot(&mut self, name: &Ident, ty: &Type) -> Result<String, String> {
        let pn = palow_name(self.tds, ty)
            .ok_or_else(|| format!("local `{}` is {}", name.val, describe(self.tds.resolve(ty))))?;
        self.lines
            .push(format!("let loc_{} = {}_stack_alloc ();", name.val, pn));
        self.slots.push(Slot {
            name: name.val.to_string(),
            palow_ty: pn.clone(),
            init: false,
        });
        Ok(pn)
    }

    /// Store into an lvalue, choosing the initialising store when the target
    /// is a slot that has not been written yet.
    fn store(&mut self, lhs: &Expr, pn: &str, value: &str) -> Result<(), String> {
        if let ExprT::Var(v) = &lhs.val {
            if let Some(i) = self.slots.iter().position(|s| s.name == *v.val) {
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
        let a = self.addr(lhs)?;
        self.lines.push(format!("{}_write {} {};", pn, a, value));
        Ok(())
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        match &s.val {
            StmtT::Decl(name, ty) => {
                self.alloc_slot(name, ty)?;
                Ok(())
            }
            StmtT::Let(name, ty, init) => {
                let v = self.rvalue(init)?;
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
                let v = self.rvalue(rhs)?;
                self.store(lhs, &pn, &v)
            }
            StmtT::Return(None) => Ok(()),
            _ => Err(format!("{} is not translated yet", stmt_kind(s))),
        }
    }

    /// Release every slot, innermost first. A slot holding a value needs
    /// `_forget` first, because deallocation must not depend on what was last
    /// stored in it.
    fn release(&mut self) {
        for i in (0..self.slots.len()).rev() {
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
    match &tds.resolve(ty).val {
        TypeT::Int { signed, width } => {
            let suffix = int_suffix(*signed, *width)?;
            if *n < BigInt::ZERO {
                if !*signed {
                    // The literal has already been reduced mod 2^width in C;
                    // reproducing that here is easy but pointless until the
                    // arithmetic that consumes it is translated.
                    return Err("a negative literal at unsigned type".to_string());
                }
                Ok(format!("({}{})", n, suffix))
            } else {
                Ok(format!("{}{}", n, suffix))
            }
        }
        TypeT::SizeT => Ok(format!("{}sz", n)),
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

fn binop(tds: &Typedefs, op: BinOp, ty: &Type) -> Result<String, String> {
    let t = tds.resolve(ty);
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
        _ => return Err(format!("an operator on {}", describe(t))),
    };
    match op {
        BinOp::Eq => return Ok("=".to_string()),
        BinOp::Lt => return Ok(format!("`{}.lt`", m)),
        BinOp::LEq => return Ok(format!("`{}.lte`", m)),
        _ => {}
    }

    // C's unsigned arithmetic wraps, so it is total and always translatable.
    // Signed arithmetic is undefined on overflow, which PAL turns into a proof
    // obligation -- and that obligation is exactly what the function's
    // `_requires` clause discharges. Since those clauses are not translated
    // yet, emitting signed arithmetic would produce a body that cannot verify
    // for a reason that has nothing to do with the memory model. Refusing it
    // here keeps the measurement honest.
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
        BinOp::Add | BinOp::Sub | BinOp::Mul => Err(
            "signed arithmetic, whose overflow obligation needs the untranslated `_requires`"
                .to_string(),
        ),
        BinOp::Div => Ok(format!("`{}.div`", m)),
        BinOp::Mod => Ok(format!("`{}.rem`", m)),
        _ => Err("an unsupported operator".to_string()),
    }
}

/// Translate a function body, or say why not. `env` must already have the
/// function's parameters pushed.
fn emit_body(tds: &Typedefs, env: Env, defn: &FnDefn) -> Result<Vec<String>, String> {
    let mut b = Body {
        tds,
        env,
        lines: Vec::new(),
        slots: Vec::new(),
        tmp: 0,
    };

    // Straight-line bodies only, with an optional trailing `return`. A
    // `return` anywhere else would have to release the slots on that path too,
    // which is a restructuring rather than a translation.
    let (last, init) = match defn.body.split_last() {
        Some((l, i)) => (Some(l), i),
        None => (None, &defn.body[..]),
    };
    for s in init {
        if matches!(s.val, StmtT::Return(_)) {
            return Err("an early return".to_string());
        }
        b.env.push_stmt(s);
        b.stmt(s)?;
    }

    let mut tail = None;
    if let Some(l) = last {
        match &l.val {
            StmtT::Return(Some(e)) => {
                tail = Some(b.rvalue(e)?);
            }
            _ => {
                b.env.push_stmt(l);
                b.stmt(l)?;
            }
        }
    }

    b.release();
    if let Some(t) = tail {
        b.lines.push(t);
    }
    Ok(b.lines)
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
