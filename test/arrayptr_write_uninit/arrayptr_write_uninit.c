#include "pal.h"
#include <stdint.h>

struct point {
    int x;
    int y;
};

// Whole-element write through an _arrayptr into *uninitialized* memory.
//
// The parent array is `array_pts_to_uninit`: every slot is allocated
// (array_spec_full_mask) but not yet initialized (no array_spec_initd). A
// whole-element assignment `*p = val` lowers to `arrayptr_write`, which only
// requires the slot's mask -- it overwrites the element wholesale instead of
// reading it first, so it verifies even though the old contents are undefined.
//
// (Contrast with a single-field write `p->x = val`, which lowers to a
// read-modify-write `arrayptr_update` and would require array_spec_initd.)
void init_via_ptr(_arrayptr struct point *p, struct point val)
  _preserves(_inline_pulse(arrayptr_pts_to $(p) $`arr))
  _requires(_inline_pulse(array_pts_to_uninit $`arr $`v))
  _requires((bool) _inline_pulse(0 <= offset_of $(p) - offset_of $`arr
    /\ offset_of $(p) - offset_of $`arr < array_spec_len $`v))
  _ensures(_inline_pulse(exists* v_new. array_pts_to $`arr 1.0R v_new))
{
  *p = val;
}
