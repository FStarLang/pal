#include "selected_file.h"

// Not named by --only-function, but this file is not under --only-function-in:
// its bodies, and those of the headers it includes, are translated and checked.
int32_t whole_caller(void)
    _ensures(return == 49)
{
    return kept(41) + header_value();
}
