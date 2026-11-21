// Tests-todo: writing a scalar field of a nested aggregate strands the
// enclosing struct's deep ownership predicate at the pre-write value.
//
// `mark_done` writes one scalar, three levels down: outer struct, anonymous
// union, inner struct. The write itself is fine. What is not fine is what the
// caller is left holding.
//
// A struct with a pointer member gets a deep ownership predicate
// `struct_Outer_own x p s` that is *keyed by the whole struct value* `x` but
// only owns what the pointer members point at. After the write the struct's
// `pts_to` is at the post-write value while the ownership is still keyed at
// the pre-write value, and the postcondition fails with
//
//   Error 228: Cannot prove:
//     struct_Outer_own (Mkstruct_Outer val_o.fld_Buffer val_o.fld_Tag
//                        (Union_Outer_anon_1_Parse
//                          (Mkstruct_Inner val_o.fld__unnamed2.v.fld_Count 3uy)))
//       1.0R _
//   In the context:
//     struct_Outer_own val_o 1.0R own_o
//
// which reads like a disagreement about the write and is really a
// disagreement about the key.
//
// Delete the `Buffer` member and this file verifies: with no pointer members
// there is no ownership predicate, and the key never matters. That is the
// whole of the difference. The union is not needed either: a write to
// `o->In.State` through a nested `struct Inner In` member fails the same way.
//
// Palow already retargets the ownership for a write `o->Tag = 3` to a direct
// scalar member: it emits `struct_Outer_own_follow`, which moves the
// ownership to the new value given that the pointer members did not change.
// The fix belongs in PAL: do the same for a write anywhere below a member the
// ownership does not read, not only for a direct member of the parameter.
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
    _requires(o->Parse._active)
{
    o->Parse.State = 3;
}
