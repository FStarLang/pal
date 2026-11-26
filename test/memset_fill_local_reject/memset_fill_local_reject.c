#include "pal.h"
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

struct flagged {
    bool valid;
    uint32_t count;
};

// 0xFF is no value of a `bool`, and a local has no uninitialized state to
// hold instead.
uint32_t scribble_local(void)
{
    struct flagged f;
    memset(&f, 0xFF, sizeof(f));
    return f.count;
}
