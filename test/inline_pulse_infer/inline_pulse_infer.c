#include "pal.h"

// Test: _inline_pulse type inference in _ensures (slprop context)
int bar()
    _ensures(_inline_pulse(pure (Int32.v $(return) > 0)))
{
    return 1;
}
