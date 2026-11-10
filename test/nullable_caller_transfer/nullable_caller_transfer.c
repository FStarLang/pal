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

/* Supplying and declining an optional parameter, from the caller's side.
   `opt_write_many` states its two outputs under a guard, which is right for
   it and wrong for a caller that knows which side of each test its own
   arguments are on. Handing over a pointer PAL owns and taking it back again
   is the ordinary shape of a conversion built out of smaller conversions. */
void forward_one(const uint64_t* Src, _out uint64_t* Dst)
    _ensures(*Dst == *Src)
{
    opt_write_many(Src, Dst, NULL);
}

/* The other way round, so that neither position is special. */
void forward_other(const uint64_t* Src, _out uint64_t* Dst)
    _ensures(*Dst == *Src)
{
    opt_write_many(Src, NULL, Dst);
}

/* Both supplied, and both recovered. */
void forward_both(const uint64_t* Src, _out uint64_t* First, _out uint64_t* Second)
    _ensures(*First == *Src)
    _ensures(*Second == *Src)
{
    opt_write_many(Src, First, Second);
}

/* Neither supplied: the guard has to be discarded twice even though nothing
   was ever behind it. */
void forward_neither(const uint64_t* Src)
{
    opt_write_many(Src, NULL, NULL);
}

/* Forwarding an optional parameter onward as an optional parameter. The
   caller cannot say which way the test goes -- that is what makes it a
   forward -- so the guard must be passed along untouched rather than opened
   and closed. */
void forward_optional(const uint64_t* Src, _nullable _out _refine(*this == *Src) uint64_t* Dst)
{
    opt_write_many(Src, Dst, NULL);
}

/* Supplying the address of a local, which is where a value read back out of
   a conversion usually lands. */
void via_local(const uint64_t* Src, _out uint64_t* Dst)
    _ensures(*Dst == *Src)
{
    uint64_t tmp;

    opt_write_many(Src, &tmp, NULL);
    *Dst = tmp;
}

/* A refined struct whose first field is itself a struct. The refinement is
   looked through to find the struct, and the struct's non-nullness comes from
   its first field's, which is the inner struct's. */
struct inner
{
    uint32_t a;
    uint32_t b;
};

_refine(this.n > 0)
typedef struct nested
{
    struct inner in;
    uint32_t n;
} nested;

void opt_nested(_nullable nested* p);

void supply_nested(nested* p)
{
    opt_nested(p);
}

void opt_nested_out(_nullable _out nested* p);

void supply_nested_out(void)
{
    nested tmp;

    opt_nested_out(&tmp);
}

/* A refined struct whose first field is a scalar, so the lemma exists and the
   supplied pointer is taken back. */
_refine(this.n > 0)
typedef struct counted
{
    uint32_t n;
    uint32_t m;
} counted;

void opt_counted(_nullable counted* p);

void supply_counted(counted* p)
{
    opt_counted(p);
}

/* An initialized object handed to an optional input: it comes back as the
   object, so the caller can read it afterwards. */
void opt_read(_nullable const uint64_t* p);

uint64_t supply_input(uint64_t* p)
    _ensures(return == *p)
{
    opt_read(p);
    return *p;
}

/* One call declining an output and a hand-managed array input: the output's
   empty guard is discarded by PAL, the array's is the author's to introduce
   and discard, and the two discards do not get in each other's way. */
void opt_out_and_array(_nullable _out uint64_t* Dst, _nullable _array const uint8_t* Buf);

void decline_out_and_array(void)
{
    _ghost_stmt(intro_unless_null_null null
        (array_pts_to uint8_t_repr 1 (SizeT.v uint8_t_alignof) null 1.0R Seq.empty));
    opt_out_and_array(NULL, NULL);
    _ghost_stmt(elim_unless_null_null null _);
}
