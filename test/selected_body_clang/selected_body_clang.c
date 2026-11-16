#include "pal.h"
#include <stdint.h>

#ifdef TEST_BAD_DECL
extern missing_type declaration_error;
#endif

uint32_t selected(uint32_t n)
    _ensures(return == n)
{
#ifdef TEST_BAD_SELECTED
    return missing_selected;
#else
    return n;
#endif
}

uint32_t unfinished(void)
#ifdef TEST_BAD_CONTRACT
    _requires(missing_contract == 0)
#endif
{
#ifdef TEST_BAD_PP
#error excluded_body_preprocessor_error
#endif
#ifdef C2PULSE
    return undeclared_call(MISSING_BODY_NAME);
#else
    return 0;
#endif
}

#ifdef TEST_BAD_REDECL
uint32_t unfinished(uint32_t n);
#endif
