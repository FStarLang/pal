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

// Runtime length constraints are explicit refinements relating the VLA field
// to the struct's length field; no length comes from the array spelling.
_refine(this.member._length == this.len)
typedef struct explicitly_refined_member {
    size_t len;
    int member[];
} explicitly_refined_member;

void use_explicitly_refined_member(explicitly_refined_member *s)
    _ensures(s->member._length == s->len)
{
}
