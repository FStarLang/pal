#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct Inner {
    uint32_t x;
} Inner;

typedef struct Outer {
    Inner in;
    uint32_t y;
} Outer;

void NeedOuter(Outer *o)
    _ensures(true)
{
    o->y = o->y;
}

uint32_t framed_if_ok(uint32_t n)
    _ensures(return == 6)
{
    Outer storage = { 0 };
    Outer *o = &storage;
    Inner *p = &o->in;
    uint32_t a = 1;
    uint32_t b = 2;
    uint32_t c = 3;

    if (n > 0)
        _requires((_slprop) _inline_pulse(Pulse.Lib.Reference.pts_to var_p (Struct_Outer.struct_outer__in_1 var_storage)) && _live(storage.in))
        _ensures((_slprop) _inline_pulse(Pulse.Lib.Reference.pts_to var_p (Struct_Outer.struct_outer__in_1 var_storage)) && _live(storage.in))
    {
        p->x = n;
    }

    NeedOuter(&storage);
    return a + b + c;
}

void framed_if_bad_fact(uint32_t n)
    _ensures(true)
{
    Outer storage = { 0 };
    Outer *o = &storage;
    Inner *p = &o->in;

    if (n > 0)
        _requires((_slprop) _inline_pulse(Pulse.Lib.Reference.pts_to var_p (Struct_Outer.struct_outer__in_1 var_storage)) && _live(storage.in))
        _ensures((_slprop) _inline_pulse(Pulse.Lib.Reference.pts_to var_p (Struct_Outer.struct_outer__in_1 var_storage)) && _live(storage.in) && (_slprop) _inline_pulse(pure False))
    {
        p->x = n;
    }

    NeedOuter(&storage);
}
