#include "pal.h"
#include <stdbool.h>

// Forward declaration with spec (as if from a header)
_pure bool negate(bool x)
        _ensures(return == !x);

// Definition without spec (spec comes from the declaration)
_pure bool negate(bool x) {
    if (x) {
        return false;
    } else {
        return true;
    }
}

void test() {
    _assert(negate(true) == false);
    _assert(negate(false) == true);
}
