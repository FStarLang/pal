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

   This is the Palow specification surface of the translation unit: the F* type
   of every parameter and the ownership its contract needs. Function bodies and
   the user's own `_requires`/`_ensures` predicates are not translated yet --
   see milestone 2 in palow.md -- so the postconditions below are the weakest
   ones that state what memory the function gives back. *)
"#;

pub fn emit_palow(tu: &TranslationUnit) -> Vec<PalowModule> {
    let tds = Typedefs::new(tu);
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
        let fndecl = match &decl.val {
            DeclT::FnDefn(d) => &d.decl,
            DeclT::FnDecl(d) => d,
            _ => continue,
        };
        match emit_fn(&tds, fndecl) {
            Ok(s) => {
                code += &s.decl;
                code += "\n";
            }
            Err(why) => {
                code += &format!("(* skipped {}: {} *)\n\n", fndecl.name.val, why);
            }
        }
    }

    vec![PalowModule {
        module_name: "PalowSpecs".to_string(),
        code,
    }]
}
