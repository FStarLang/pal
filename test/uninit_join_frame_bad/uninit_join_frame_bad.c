#include "pal.h"
#include <stdint.h>

void uninitialized_after_join(int *p, _Bool write)
{
    int x;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. R.value int32_t_ctype int32_t_repr int32_t_alignof $&(*p) 1.0R v index_p))
    {
        *p = 1;
    }
    _assert(_live(x));
}
