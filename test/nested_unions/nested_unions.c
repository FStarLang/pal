#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

union ab {
    int a;
    bool b;
};

struct stru {
    int8_t tag;
    union ab payload;
};

union nested {
    union ab x;
    char z;
};

union nested2 {
    union ab x;
    char z;
    struct stru strufield;
};
