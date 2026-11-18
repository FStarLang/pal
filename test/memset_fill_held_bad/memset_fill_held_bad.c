#include "pal.h"
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

struct record {
    bool valid;
    uint32_t count;
};

// The object still holds a value, which the fill would silently destroy: the
// caller must forget it first.
void scribble_held(struct record *r)
    _ensures(r->valid)
{
    memset(r, 0xFF, sizeof(*r));
}
