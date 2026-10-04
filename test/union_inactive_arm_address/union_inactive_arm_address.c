#include "pal.h"
#include <stdint.h>

// `&u.arm` is address arithmetic in C, valid whichever arm was last stored.
// PAL lowers it to the arm's address projection, which needs no resource and
// grants no ownership: a read or write through the pointer still needs the
// arm to be active.

typedef struct _SCRATCH {
    uint32_t Other;
    union {
        uint64_t A;
        uint64_t B;
    } Crc;
} SCRATCH;

typedef struct _OUTER {
    uint32_t Tag;
    union {
        SCRATCH Scratch;
        uint32_t Raw;
    } Arm;
} OUTER;

// Stores the pointer for a later write; no ownership needed now.
void defer_write(_plain uint64_t *out);

// Addresses of two different arms, neither of which is known to be active.
void push_both(SCRATCH *s)
{
    defer_write(&s->Crc.A);
    defer_write(&s->Crc.B);
}

// The same through an active arm of an enclosing union.
void push_nested(OUTER *o)
    _requires(o->Arm.Scratch._active)
    _ensures(o->Arm.Scratch._active)
{
    defer_write(&o->Arm.Scratch.Crc.A);
    defer_write(&o->Arm.Scratch.Crc.B);
}

// Through the active arm the address gives back the arm's cell.
void write_active(SCRATCH *s)
    _requires(s->Crc.A._active)
    _ensures(s->Crc.A._active && s->Crc.A == 7)
{
    uint64_t *p = &s->Crc.A;
    *p = 7;
}

void set7(uint64_t *p)
    _ensures(*p == 7);

// An owning callee gets the active arm's cell through its address.
void call_active(SCRATCH *s)
    _requires(s->Crc.B._active)
    _ensures(s->Crc.B._active && s->Crc.B == 7)
{
    set7(&s->Crc.B);
}

// Negative: the address of an inactive arm gives no ownership of it.
void write_inactive(SCRATCH *s)
    _requires(s->Crc.A._active)
{
    uint64_t *p = &s->Crc.B;
    *p = 7;
}

// Negative: nor can it be read.
uint64_t read_inactive(SCRATCH *s)
    _requires(s->Crc.A._active)
{
    uint64_t *p = &s->Crc.B;
    return *p;
}
