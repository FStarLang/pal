#include "selected_file.h"

// This file is not under --only-function-in, so this body is translated and
// its wrong postcondition fails, though --only-function does not name it.
int32_t whole_caller(void)
    _ensures(return == 50)
{
    return kept(41) + header_value();
}
