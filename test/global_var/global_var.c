#include "pal.h"
#include <stdbool.h>

_pure bool my_true = true;
_pure bool my_false = false;

void test() {
    _assert(my_true == true);
    _assert(my_false == false);
    _assert(my_true != my_false);
}
