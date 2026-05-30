#include "pal.h"
#include <stdint.h>

_refine(this._length == 64)
_array
typedef uint8_t *hash;

/*
Should be translated to:

ghost fn func_first_byte (var_h: ty_hash)
  requires (ty_hash__pred var_h 'p_h_0 'val_h_0 'val_h_1)
  requires pure False
  returns return_1 : ty_uint8_t
  ensures rewrites_to return_1 (old (array_read var_h 0sz))
{
  unreachable ()
}
*/
_letimpure(uint8_t first_byte(const hash h), h[0])

void foo(hash h) _requires(first_byte(h) == 0) {}