#include "pal.h"
#include <stdint.h>

union value {
    uint32_t number;
    uint64_t other;
};

struct envelope {
    union value data;
};

union wrapped {
    struct envelope envelope;
    uint64_t reserved[2];
};

/* The outer tag does not establish the active arm of the inner union. */
union wrapped copy_unknown(const union wrapped *input)
    _requires(input->envelope._active)
{
    return *input;
}
