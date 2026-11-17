#include "pal.h"

/* Markers in a shared header reach every translation unit that includes it. */
_pal_admit int platform_identity(int x) _ensures(return == x);
_pal_ignore int platform_unused(int x);
