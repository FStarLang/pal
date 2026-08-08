#include "pal.h"

#include <stdint.h>

typedef struct _RECORD
{
    int32_t Code;
    uint32_t Info;
} RECORD;

int test_negative_literal() {
    int x = -10;
    int y = -100;
    return x + y;
}

// A negative literal in a record field or an assignment must be parenthesized:
// F* lexes `=-` and `:=-` as single operators.
RECORD test_negative_literal_field(void) {
    RECORD record = {.Code = -2084828230L, .Info = 0};
    record.Code = -1;
    return record;
}
