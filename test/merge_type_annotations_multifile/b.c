#include "pal.h"

const char *name_left(int status, const char *fallback);

_plain const char *name_right(int status, _plain const char *fallback);

_plain const char *call_right(int status, _plain const char *fallback)
{
    return name_right(status, fallback);
}
