#include "pal.h"

// A shared Pulse module, defined in a header rather than in any one .c file.
// Two translation units below use it; neither could define it, because the
// definition would then be duplicated, and a module defined twice in one
// translation unit is an error.
//
// The pruner has to keep this declaration on the strength of the references to
// it in the annotations further down, and has to keep `sign` -- which nothing
// else in either .c file mentions -- because the module's own body does.
_include_pulse(
    Vocab,
    let nonneg (x: FStar.Int32.t) : prop =
        FStar.Int32.v (Func_sign.func_sign x) >= 0)

_pure
int sign(int x)
    _ensures((x >= 0 ==> return == 1) && (x < 0 ==> return == -1));

int clamp(int x)
    _ensures(_inline_pulse(pure (Vocab.nonneg $(return))));
