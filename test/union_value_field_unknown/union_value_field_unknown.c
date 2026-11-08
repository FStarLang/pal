#include "pal.h"
#include <stdint.h>

union value {
    struct {
        uint32_t first;
        uint32_t last;
    } pair;
    uint64_t word;
};

uint32_t read_unknown_field(union value input)
{
    return input.pair.first;
}
