#define HELPER_VALUE 3
#include "selected_file_static.h"

// Named by --only-function, as is `helper`: this file's copy of it is
// translated and checked.
int32_t kept(void)
    _ensures(return == 4)
{
    return helper() + 1;
}
