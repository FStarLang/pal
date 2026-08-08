#include "parity.h"

_include_pulse(
    Parity_Pal,
    unfold let is_odd_or_zero (odd: bool) (v: FStar.UInt32.t) (r: bool) : slprop =
        pure (r == (odd || FStar.UInt32.v v = 0)))

_Bool
odd_or_zero(uint32_t v)
{
    return ((v % 2) == 1) || (v == 0);
}
