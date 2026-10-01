#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct buffer_view {
    void *base;
    uint32_t length;
};

struct arrayptr_view {
    _arrayptr void *base;
    uint32_t length;
};

_include_pulse(VoidptrArrayCast,
  let bytes_of (p: Pulse.Lib.C.CoreRef.core_ref) : array $type(uint8_t) =
    Pulse.Lib.C.Array.ref_to_array
      (Pulse.Lib.C.CoreRef.core_to_ref $type(uint8_t) p)
)

uint8_t read_byte(struct buffer_view *view, uint32_t off)
  _requires(off < view->length)
  _preserves(_inline_pulse(
    exists* (s: full_array_spec $type(uint8_t)).
      array_pts_to (VoidptrArrayCast.bytes_of $(view->base)) 1.0R s **
      pure (array_spec_len s == UInt32.v $(view->length)) **
      pure (array_spec_initd s (UInt32.v $(off)))))
{
    _arrayptr uint8_t *p = (uint8_t *)view->base + off;
    uint8_t value = p[0];
    _ghost_stmt(arrayptr_drop $(p));
    return value;
}

void *advance_raw(struct buffer_view *view, uint32_t off)
  _requires(off < view->length)
{
    void *p = (uint8_t *)view->base + off;
    return p;
}

void *advance_arrayptr_raw(struct arrayptr_view *view, uint32_t off)
  _requires(off < view->length)
{
    void *p = (uint8_t *)view->base + off;
    return p;
}
