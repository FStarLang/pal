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

// Runtime length constraints are explicit refinements on the struct field.
struct explicitly_refined_member {
    int tag;
    int member[0] _refine(this._length == 2);
};

void use_explicitly_refined_member(struct explicitly_refined_member *s)
    _requires(s->member._length == 2)
{
}
