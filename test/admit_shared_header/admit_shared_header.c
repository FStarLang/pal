#include "platform.h"
#include <stdint.h>

int caller(void) _ensures(return == 1) { return platform_identity(1); }
