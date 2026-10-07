//! Computing `sizeof`, `_Alignof` and `offsetof` for C types.
//!
//! PAL used to translate `sizeof(T)` to an opaque `Pulse.Lib.C.Sizeof.c_sizeof`
//! applied to the *F\** type that `T` maps to. That was unsound in spirit (two
//! different C types can map to the same F\* type, and then their `c_sizeof`s
//! are forced to be equal) and unusable in practice (nothing could ever compute
//! a concrete size, so every fact about sizes had to be an axiom).
//!
//! Instead we take the layout straight from clang, which already knows the
//! target ABI. Named types (structs, unions, typedefs) get their size,
//! alignment and field offsets recorded in an [`ir::LayoutTable`] by the
//! frontend, and this module looks them up. `sizeof(T)` then emits a plain
//! `SizeT` literal.
//!
//! See `palow.md`, milestone 3.

use crate::ir::{self, LayoutKey, LayoutTable, TypeRefKind};

/// The clang-computed layout of named types.
pub struct LayoutCtx<'a> {
    pub table: &'a LayoutTable,
}

impl<'a> LayoutCtx<'a> {
    pub fn of_tu(tu: &'a ir::TranslationUnit) -> LayoutCtx<'a> {
        LayoutCtx { table: &tu.layouts }
    }

    fn named(&self, kind: &TypeRefKind) -> Option<&ir::TypeLayout> {
        self.table.get(&LayoutKey::of_type_ref(kind))
    }

    /// Byte offset of field `field` within the named type `kind`.
    ///
    /// Not consumed yet; the byte-level aggregate predicates that need it are
    /// milestone 4 of `palow.md`.
    #[allow(dead_code)]
    pub fn offset_of(&self, kind: &TypeRefKind, field: &str) -> Option<u64> {
        self.named(kind)?
            .field_offsets
            .iter()
            .find(|(n, _)| &**n == field)
            .map(|(_, o)| *o)
    }

    /// Bit offset of bit-field `field` within the named type `kind`, counted
    /// from the start of the object. A bit-field has no byte offset: the
    /// storage unit it shares with its neighbours does.
    pub fn bit_offset_of(&self, kind: &TypeRefKind, field: &str) -> Option<u64> {
        self.named(kind)?
            .field_bit_offsets
            .iter()
            .find(|(n, _)| &**n == field)
            .map(|(_, o)| *o)
    }
}
