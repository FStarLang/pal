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
//! frontend; everything else is derived structurally here. `sizeof(T)` then
//! emits a plain `SizeT` literal.
//!
//! See `palow.md`, milestone 3.

use crate::ir::{self, LayoutKey, LayoutTable, TypeRefKind, TypeT};

/// Everything needed to size a C type: the clang-computed layout of named
/// types plus the target's pointer width.
pub struct LayoutCtx<'a> {
    pub table: &'a LayoutTable,
    pub pointer_size: u64,
}

impl<'a> LayoutCtx<'a> {
    pub fn of_tu(tu: &'a ir::TranslationUnit) -> LayoutCtx<'a> {
        LayoutCtx {
            table: &tu.layouts,
            pointer_size: tu.pointer_size,
        }
    }

    fn named(&self, kind: &TypeRefKind) -> Option<&ir::TypeLayout> {
        self.table.get(&LayoutKey::of_type_ref(kind))
    }

    /// Size of `ty` in bytes, or `None` if the type has no statically known
    /// size (incomplete types, flexible array members, error types).
    pub fn size_of(&self, ty: &ir::Type) -> Option<u64> {
        match &ty.val {
            // `sizeof(void)` is 1 as a GNU extension, and clang accepts it.
            TypeT::Void => Some(1),
            TypeT::Bool => Some(1),
            TypeT::Int { width, .. } | TypeT::Float { width } => {
                Some(u64::from(*width).div_ceil(8).max(1))
            }
            TypeT::SizeT | TypeT::PtrdiffT => Some(self.pointer_size),
            TypeT::Pointer(..) | TypeT::FnPtr { .. } => Some(self.pointer_size),
            TypeT::FixedArray(elem, n) => self.size_of(elem)?.checked_mul(*n),
            TypeT::TypeRef(kind) => self.named(kind).map(|l| l.size),
            TypeT::Refine(inner, _)
            | TypeT::RefineAlways(inner, _)
            | TypeT::RefineUninit(inner, _)
            | TypeT::RefineValue(inner, ..)
            | TypeT::Plain(inner)
            | TypeT::Nullable(inner) => self.size_of(inner),
            // Ghost-only types have no runtime representation, and a flexible
            // array member contributes nothing to its enclosing struct's size.
            TypeT::SpecInt | TypeT::SpecNat | TypeT::SLProp | TypeT::FlexArray(_) => None,
            TypeT::Unknown | TypeT::Error => None,
        }
    }

    /// Alignment of `ty` in bytes, or `None` if unknown.
    pub fn align_of(&self, ty: &ir::Type) -> Option<u64> {
        match &ty.val {
            TypeT::TypeRef(kind) => self.named(kind).map(|l| l.align),
            TypeT::FixedArray(elem, _) => self.align_of(elem),
            TypeT::Refine(inner, _)
            | TypeT::RefineAlways(inner, _)
            | TypeT::RefineUninit(inner, _)
            | TypeT::RefineValue(inner, ..)
            | TypeT::Plain(inner)
            | TypeT::Nullable(inner) => self.align_of(inner),
            TypeT::FlexArray(elem) => self.align_of(elem),
            // Scalars are naturally aligned on every target PAL supports.
            _ => self.size_of(ty),
        }
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
}
