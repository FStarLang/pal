#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

// A conditional expression has type `int`; storing it into a narrower
// object converts it. When the conditional is hoisted into a prelude
// binding, the conversion is emitted from the binding, and must use the
// same total, modular `Int.Cast` conversions as any other cast.

struct flags {
    uint8_t flag : 1;
    uint8_t small;
};

void set_flag_from_mode(struct flags *s, unsigned mode)
  _ensures(s->flag == (mode == 1 ? 1 : 0))
{
    s->flag = (mode == 1u) ? 1 : 0;
}

void set_flag_from_bool(struct flags *s, bool on)
  _ensures(s->flag == (on ? 1 : 0))
{
    s->flag = on ? 1 : 0;
}

void set_small(struct flags *s, bool on)
  _ensures(s->small == (on ? 7 : 3))
{
    s->small = on ? 7 : 3;
}

int16_t narrow_signed(bool on)
  _ensures(return == (on ? -2 : 5))
{
    int16_t r = on ? -2 : 5;
    return r;
}
