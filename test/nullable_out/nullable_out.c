#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// An optional output, the C `_Out_opt_` shape: the callee writes through the
// pointer only when it is non-null, so the value postcondition has to live
// inside the unless_null. Writing it as a _refine on the parameter puts it
// there; a function-level _ensures could not, because it would have to deref a
// pointer whose pts_to is guarded.
void opt_write(
    const uint64_t* Src,
    _nullable _out _refine(*this == *Src) uint64_t* Dst)
{
    if (Dst != NULL)
    {
        *Dst = *Src;
    }
}

// The inverted shape: an early return under a null test, with the write in the
// fall-through rather than in a then-branch.
void opt_write_early_return(
    const uint32_t* Src,
    _nullable _out _refine(*this == *Src) uint32_t* Dst)
{
    if (Dst == NULL)
    {
        return;
    }

    *Dst = *Src;
}

// Several optional outputs on one function, each independently guarded, which
// is how the media header converters in practice spell _Out_opt_.
void opt_write_many(
    const uint64_t* Src,
    _nullable _out _refine(*this == *Src) uint64_t* First,
    _nullable _out _refine(*this == *Src) uint64_t* Second)
{
    if (First != NULL)
    {
        *First = *Src;
    }

    if (Second != NULL)
    {
        *Second = *Src;
    }
}

// A nullable array output. The array's length is not known here, so nothing is
// indexed; what the case exercises is that eliminating the guard hands back an
// ordinary array pts_to, good enough to pass the array on to a callee that
// demands full ownership.
void takes_array(_array uint8_t* a);

void opt_forward_array(_nullable _array uint8_t* Dst)
{
    if (Dst != NULL)
    {
        takes_array(Dst);
    }
}

struct pair
{
    uint64_t lo;
    uint64_t hi;
};

void fill_pair(_out struct pair* p)
    _ensures(p->lo == 0 && p->hi == 0);

// The shape the media header converters actually use: an optional output that
// is not written directly but handed to a callee which initializes it. The
// _refine states what the callee guarantees, so the caller's optional
// postcondition is the callee's unconditional one under the guard.
void opt_fill_pair(_nullable _out _refine(this->lo == 0 && this->hi == 0) struct pair* Dst)
{
    if (Dst != NULL)
    {
        fill_pair(Dst);
    }
}
