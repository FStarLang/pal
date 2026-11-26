#include "pal.h"

int pick(_nullable const char *fallback);

int length(_nullable const char *s)
    _ensures(return >= 0);
