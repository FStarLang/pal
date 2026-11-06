#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A loop condition `n < 4 && (more = advance(it))` whose call updates a
 * deeply owned object and returns a Boolean the postcondition ties to the new
 * value. C promotes the `_Bool` operand of `&&` to `int` and tests it again.
 * PAL must test the call's result itself: had it kept the `int` round trip,
 * the cast's value would sit in the join's existential together with the
 * object's ownership, and the join could not be proved. */

struct cursor {
    uint32_t *data;
    uint32_t pos;
    uint32_t len;
};

struct holder {
    struct cursor *it;
};

bool advance(struct cursor *c)
  _requires(c->pos <= c->len)
  _ensures(c->pos <= c->len)
  _ensures(return == (c->pos < c->len));

uint32_t remaining(struct cursor *c)
  _requires(c->pos < c->len)
  _ensures(c->pos == _old(c->pos) && c->len == _old(c->len))
  _ensures(return == c->len - c->pos - 1);

uint16_t walk(struct holder h)
  _requires((_slprop)_inline_pulse(
      exists* v o.
          Struct_cursor.struct_cursor_pts_to $(h.it) 1.0R v **
          Struct_cursor.struct_cursor_own v 1.0R o **
          pure (UInt32.v v.fld_pos <= UInt32.v v.fld_len)))
  _ensures((_slprop)_inline_pulse(
      exists* v o.
          Struct_cursor.struct_cursor_pts_to $(h.it) 1.0R v **
          Struct_cursor.struct_cursor_own v 1.0R o))
  _ensures(return <= 4)
{
    uint16_t n = 0;
    bool more = false;
    while (n < 4 && (more = advance(h.it)))
      _invariant(_live(n) && _live(more))
      _invariant(n <= 4)
      _invariant((_slprop)_inline_pulse(
          exists* v o.
              Struct_cursor.struct_cursor_pts_to $(h.it) 1.0R v **
              Struct_cursor.struct_cursor_own v 1.0R o **
              pure (UInt32.v v.fld_pos <= UInt32.v v.fld_len)))
    {
        remaining(h.it);
        n = n + 1;
    }
    return n;
}
