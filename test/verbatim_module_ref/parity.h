#pragma once
#include "pal.h"

#include <stdint.h>

// A pure function declared in a header, so the pruner sees it as a non-root
// declaration. Nothing in the translation unit calls it: its only reference is
// the verbatim text of the contract below, which names the generated module
// Func_value_is_odd directly.
_pure
_Bool
value_is_odd(uint32_t v)
    _ensures(return == ((v % 2) == 1));

_Bool
odd_or_zero(uint32_t v)
    _ensures(
        _inline_pulse(
            Parity_Pal.is_odd_or_zero
                (Func_value_is_odd.func_value_is_odd $(v))
                $(v)
                $(return)));
