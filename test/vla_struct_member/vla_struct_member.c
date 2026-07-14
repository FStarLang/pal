#include "pal.h"
#include <stddef.h>

// An incomplete flexible-array member is modeled as a variable-length array.
struct incomplete_member {
    int tag;
    int member[];
};

void constrain_incomplete_member(struct incomplete_member *s, size_t length)
    _requires(s->member._length == length)
{
}

// PAL treats the GNU zero-length spelling the same way: the written zero is
// ignored rather than becoming an implicit runtime length constraint.
struct zero_length_member {
    int tag;
    int member[0];
};

void constrain_zero_length_member(struct zero_length_member *s, size_t length)
    _requires(s->member._length == length)
{
}

// Runtime length constraints are explicit FieldDecl refinements relating the
// VLA member to the enclosing struct's length field; no length comes from the
// array spelling itself.
struct explicitly_refined_member {
    size_t len;
    int member[] _refine(this.member._length == this.len);
};
