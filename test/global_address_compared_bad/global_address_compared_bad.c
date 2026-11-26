#include "pal.h"
#include <stddef.h>
#include <stdint.h>

uint32_t tag;

_let(_slprop holds(uint32_t *a, uint32_t v),
     _inline_pulse(uint32_t_pts_to $(a) 1.0R $(v)))

/* Besides comparing the two addresses, this callee asks for the pointee of
 * one of them, so a caller that passes `&tag` must own `tag`. */
static uint32_t read_same(_plain uint32_t *p, _plain uint32_t *q)
    _ghost_arg(uint32_t value)
    _requires(p == q)
    _preserves(holds(p, value))
    _ensures(return == value) {
  return *p;
}

uint32_t read_tag_address(void) { return read_same(&tag, &tag); }

/* Calling it holding nothing must fail: it needs `tag`. */
void check_read_tag_address(void) {
  _ghost_stmt(let _ = Func_read_tag_address.func_read_tag_address (); ());
}
