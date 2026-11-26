#include "pal.h"
#include <stdint.h>

// Named by --only-function: translated and checked.
int32_t kept(int32_t input)
    _requires(input < 100)
    _ensures(return == input + 1)
{
    return input + 1;
}

// Not named: only its declaration is translated. Under PAL (PALOW) the body
// calls an undeclared function, a clang error; it is in a body PAL does not
// translate, so it is reported as a warning and the translation stands.
int32_t excluded(void)
{
#ifdef PALOW
    return undeclared_function(1);
#else
    return 0;
#endif
}
