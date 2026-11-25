#include "pal.h"
#include <stddef.h>
#include <stdint.h>

uint32_t tag;

/* Besides the NULL test, this callee asks for the pointee, so a caller that
 * passes `&tag` must own `tag`. */
static uint32_t read_tag(_plain uint32_t *p)
    _requires(p != NULL)
    _ghost_arg(uint32_t value)
    _preserves(_inline_pulse(uint32_t_pts_to $(p) 1.0R $(value)))
    _ensures(return == value) {
  return *p;
}

uint32_t read_tag_address(void) { return read_tag(&tag); }

/* Calling it holding nothing must fail: it needs `tag`. */
void check_read_tag_address(void) {
  _ghost_stmt(let _ = Func_read_tag_address.func_read_tag_address (); ());
}
