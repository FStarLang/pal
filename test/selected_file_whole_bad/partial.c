#include "selected_file.h"

// Named by --only-function: translated and checked.
int32_t kept(int32_t input)
    _requires(input < 100)
    _ensures(return == input + 1)
{
    return input + 1;
}

// Not named, and this file is under --only-function-in: only its declaration
// is translated, so PAL never sees the mixed-sign builtin it rejects.
_Bool excluded(_out uint32_t *result)
{
    return __builtin_mul_overflow(-1, 2u, result);
}
