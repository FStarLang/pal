//! `layout_table.json`: every layout clang computed that Palow may have used.
//!
//! Palow writes the target's layout into its output as numbers: a struct's
//! `_sizeof`, `_alignof` and `_offsetof_` definitions, a `sizeof` in code as
//! the literal it evaluates to, and an `offsetof` that the frontend has
//! already folded to an integer. They are only as right as the layout clang
//! computed, and the program runs with the layout its own compiler computed.
//! This file is the table those numbers come from, so that a build can ask
//! its compiler the same questions.
//!
//! It is taken before `prune`, so it covers every type the unit defines and
//! not only the ones that survive into the output: a folded `offsetof` leaves
//! no trace of the type it was computed from. Each named type comes with
//! where it is defined, which is the only way to say which C type an
//! anonymous one is. A typedef also comes with the size and alignment Palow
//! gives it, which is that of the type it names: a typedef that changes its
//! type's alignment is invisible to Palow, and has to be visible here.

use std::collections::HashMap;

use serde::Serialize;

use crate::ir::{DeclT, LayoutKey, TranslationUnit, Type, TypeRefKind, TypeT};

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FieldOffset {
    name: String,
    offset: u64,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct FieldBitOffset {
    name: String,
    bit_offset: u64,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct TypeInfo {
    kind: &'static str,
    name: String,
    size: u64,
    align: u64,
    field_offsets: Vec<FieldOffset>,
    field_bit_offsets: Vec<FieldBitOffset>,
    /// Where the definition is: the same convention as
    /// `source_range_info.json`.
    #[serde(skip_serializing_if = "Option::is_none")]
    uri: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    range: Option<lsp_types::Range>,
    /// For a typedef, the size and alignment of the type it names, worked out
    /// the way the Palow emitter does: through typedefs, from the scalar's
    /// width or the aggregate's layout. `None` where Palow has no answer.
    #[serde(skip_serializing_if = "Option::is_none")]
    resolved_size: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    resolved_align: Option<u64>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Snapshot {
    target_triple: String,
    big_endian: bool,
    pointer_size: u64,
    types: Vec<TypeInfo>,
}

/// What `palow_sizeof` and `palow_alignof` would say, kept in step with them
/// by hand: this is the claim being checked, not a second opinion.
struct Resolver<'a> {
    tu: &'a TranslationUnit,
    typedefs: HashMap<&'a str, &'a Type>,
}

impl Resolver<'_> {
    fn resolve<'b>(&'b self, ty: &'b Type) -> &'b Type {
        let mut ty = ty;
        for _ in 0..64 {
            match &ty.val {
                TypeT::TypeRef(TypeRefKind::Typedef(n)) => match self.typedefs.get(&*n.val) {
                    Some(body) => ty = body,
                    None => return ty,
                },
                _ => return ty,
            }
        }
        ty
    }

    fn aggregate(&self, kind: &TypeRefKind) -> Option<(u64, u64)> {
        self.tu
            .layouts
            .get(&LayoutKey::of_type_ref(kind))
            .map(|l| (l.size, l.align))
    }

    fn size(&self, ty: &Type) -> Option<u64> {
        match &self.resolve(ty).val {
            TypeT::Bool => Some(1),
            TypeT::Int { width, .. } | TypeT::Float { width } => Some((*width / 8) as u64),
            TypeT::SizeT | TypeT::PtrdiffT | TypeT::Pointer(..) | TypeT::FnPtr { .. } => Some(8),
            TypeT::FixedArray(t, n) => self.size(t).map(|s| s * n),
            TypeT::TypeRef(k @ (TypeRefKind::Struct(_) | TypeRefKind::Union(_))) => {
                self.aggregate(k).map(|l| l.0)
            }
            TypeT::Refine(t, _)
            | TypeT::RefineAlways(t, _)
            | TypeT::RefineUninit(t, _)
            | TypeT::RefineValue(t, ..)
            | TypeT::Plain(t)
            | TypeT::Nullable(t) => self.size(t),
            _ => None,
        }
    }

    fn align(&self, ty: &Type) -> Option<u64> {
        match &self.resolve(ty).val {
            TypeT::FixedArray(t, _) => self.align(t),
            TypeT::TypeRef(k @ (TypeRefKind::Struct(_) | TypeRefKind::Union(_))) => {
                self.aggregate(k).map(|l| l.1)
            }
            _ => self.size(ty),
        }
    }
}

impl Snapshot {
    pub fn take(tu: &TranslationUnit) -> Snapshot {
        let mut defs = HashMap::new();
        let mut typedefs = HashMap::new();
        for d in &tu.decls {
            let key = match &d.val {
                DeclT::StructDefn(s) => LayoutKey::Struct(s.name.val.clone()),
                DeclT::UnionDefn(u) => LayoutKey::Union(u.name.val.clone()),
                DeclT::Typedef(t) => {
                    typedefs.entry(&*t.name.val).or_insert(&*t.body);
                    LayoutKey::Typedef(t.name.val.clone())
                }
                _ => continue,
            };
            defs.entry(key).or_insert_with(|| d.loc.location().clone());
        }
        let r = Resolver { tu, typedefs };
        let types = tu
            .layouts
            .iter()
            .map(|(key, l)| {
                let (kind, name) = match key {
                    LayoutKey::Typedef(n) => ("typedef", n),
                    LayoutKey::Struct(n) => ("struct", n),
                    LayoutKey::Union(n) => ("union", n),
                };
                let loc = defs.get(key);
                let body = match key {
                    LayoutKey::Typedef(n) => r.typedefs.get(&**n).copied(),
                    _ => None,
                };
                TypeInfo {
                    kind,
                    name: name.to_string(),
                    size: l.size,
                    align: l.align,
                    field_offsets: l
                        .field_offsets
                        .iter()
                        .map(|(n, o)| FieldOffset {
                            name: n.to_string(),
                            offset: *o,
                        })
                        .collect(),
                    field_bit_offsets: l
                        .field_bit_offsets
                        .iter()
                        .map(|(n, o)| FieldBitOffset {
                            name: n.to_string(),
                            bit_offset: *o,
                        })
                        .collect(),
                    uri: loc.map(|l| crate::source_range_info::path_to_uri(&l.file_name)),
                    range: loc.map(|l| l.range.to_lsp()),
                    resolved_size: body.and_then(|b| r.size(b)),
                    resolved_align: body.and_then(|b| r.align(b)),
                }
            })
            .collect();
        Snapshot {
            target_triple: tu.target_triple.to_string(),
            big_endian: tu.big_endian,
            pointer_size: tu.pointer_size,
            types,
        }
    }

    pub fn serialize(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
}
