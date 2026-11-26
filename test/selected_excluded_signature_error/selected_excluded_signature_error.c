#include "pal.h"
#include <stdint.h>

int32_t kept(int32_t input)
    _requires(input < 100)
    _ensures(return == input + 1)
{
    return input + 1;
}

// Not named, but its declaration is translated: under PAL (PALOW) its
// parameter has an undeclared type, an error that still fails the translation.
#ifdef PALOW
int32_t excluded(undeclared_type input)
#else
int32_t excluded(int32_t input)
#endif
{
    return 0;
}
