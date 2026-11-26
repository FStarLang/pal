#define HELPER_VALUE 4
#include "selected_file_static.h"

// This file is not under --only-function-in and does not use `helper`, so its
// copy -- which would not meet the contract -- is pruned as it would be
// without a selection, although --only-function names `helper`.
int32_t whole_value(void)
    _ensures(return == 5)
{
    return 5;
}
