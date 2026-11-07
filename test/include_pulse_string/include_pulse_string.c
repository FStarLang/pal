#include "pal.h"
#include <stdint.h>

// String literals inside `_include_pulse` are F* text and must survive
// verbatim: the `"opaque_to_smt"` attribute and the name `reveal_opaque`
// takes are both strings.  PAL's lexer used to abort the whole process on
// any string literal here ("Repeated combinator making no progress"), and
// dropped the quotes on output.
_include_pulse(StringBearing,
  [@@"opaque_to_smt"]
  let small (x: FStar.UInt32.t) : prop = FStar.UInt32.v x < 10

  let reveal_small (x: FStar.UInt32.t)
  : FStar.Pervasives.Lemma (small x <==> FStar.UInt32.v x < 10)
  = FStar.Pervasives.reveal_opaque "StringBearing.small" (small x)

  let escaped : string = "a \"quoted\" word"
)

uint32_t three(void)
  _ensures(return < 10)
{
  uint32_t r = 3;
  _ghost_stmt(StringBearing.reveal_small $(r));
  return r;
}
