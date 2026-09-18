//! PAL primitives: compiler builtins that stand for Pulse library functions.
//!
//! A compiler builtin has no C declaration for PAL to translate, so a call to
//! one cannot be an ordinary `FnCall`: there is no `Func_<name>` module to
//! name, `check` would reject it as an unknown function, and type inference
//! would have nothing to look up. The front end instead emits a call under a
//! reserved `__pal_` name, and this module is the single place that says what
//! such a name means.
//!
//! Every entry must be a DEFINITION in PAL's Pulse library, not an assumption.
//! A builtin whose meaning cannot be written down in Pulse -- one that reads a
//! machine register, say -- belongs in `Pulse.Lib.C.Assumptions` with a written
//! justification, not here, precisely so that it is counted as trusted.

use crate::ir::TypeT;

struct Prim {
    /// The reserved name the front end emits.
    name: &'static str,
    /// The Pulse library function it stands for.
    target: &'static str,
    /// The result type, for inference. Arguments are not checked: the front end
    /// only ever emits a primitive at the arity and argument types its library
    /// function has.
    ret: fn() -> TypeT,
}

const PRIMS: &[Prim] = &[Prim {
    // `__builtin_bswap64`: reverse the bytes of a 64-bit value.
    // `Pulse.Lib.C.UInt64.bswap64` is defined in terms of shifts and masks, so
    // a caller that needs to reason about the result can unfold it.
    name: "__pal_bswap64",
    target: "Pulse.Lib.C.UInt64.bswap64",
    ret: || TypeT::Int {
        signed: false,
        width: 64,
    },
}];

fn lookup(name: &str) -> Option<&'static Prim> {
    PRIMS.iter().find(|p| p.name == name)
}

/// The Pulse library function `name` stands for, if it is a primitive.
pub fn target(name: &str) -> Option<&'static str> {
    lookup(name).map(|p| p.target)
}

/// The result type of the primitive `name`, if it is one.
pub fn ret_type(name: &str) -> Option<TypeT> {
    lookup(name).map(|p| (p.ret)())
}

/// Whether `name` is a PAL primitive.
pub fn is_prim(name: &str) -> bool {
    lookup(name).is_some()
}
