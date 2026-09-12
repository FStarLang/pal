// Tests-todo: writing a scalar field of a nested aggregate strands the
// enclosing struct's deep predicate at the pre-write value.
//
// `mark_done` writes one scalar, three levels down: outer struct, anonymous
// union, inner struct. The write itself is fine. What is not fine is what the
// caller is left holding.
//
// A struct with a pointer member gets a deep predicate `struct_outer__pred`
// that is *indexed by the whole struct value* but only owns what the pointer
// members point at. So after the write there are two chunks: a `pts_to` at the
// post-write value, and a deep predicate still indexed at the pre-write value.
// The prover matches the stale one first and reports
//
//   Could not prove equality of
//     `pts_to var_o (Mkstruct_outer ... (Field_Outer_anon_1__Parse
//                     (Mkstruct_inner ... (int32_to_uint8 3l))))`
//     `pts_to var_o val_o_0`
//
// which reads like a disagreement about the write and is really a disagreement
// about the index.
//
// Delete the `Buffer` member and this file verifies: with no pointer members
// the deep predicate has nothing to own, and the index never matters. That is
// the whole of the difference. (Dropping the member also renumbers the
// anonymous union to `___unnamed1`, so the precondition below has to follow;
// nothing else changes.)
//
// The fix belongs in PAL: index the deep predicate by only the
// ownership-relevant projection of the struct -- its pointer members -- so a
// write to any other member cannot move it. Today the workaround is a
// hand-written ghost step that unfolds at the old index, rewrites the pointer
// members, and folds at the new one; it is a theorem, but one per struct.
//
// The union-arm precondition below is a separate, known limitation: an
// untagged union has no discriminant, so which arm is live has to be said.
#include "pal.h"
#include <stdint.h>

struct Inner
{
    uint32_t Count;
    uint8_t State;
};

struct Outer
{
    uint32_t* Buffer;
    uint32_t Tag;
    union {
        struct Inner Parse;
        uint32_t Other;
    };
};

void
mark_done(struct Outer* o)
    _requires(_inline_pulse(
        pure (Union_Outer_anon_1.Field_Outer_anon_1__Parse?
                ((!$(o)).Struct_Outer.struct_outer___unnamed2))))
{
    o->Parse.State = 3;
}
