#include "pal.h"
#include <stdint.h>
#include <string.h>

struct sample {
    int64_t wide;
    uint32_t narrow;
};

// A local holds a value, not bytes, so a nonzero fill of a whole local is a
// write of the one value those bytes encode: two's complement for a signed
// member, whatever value the local held before.
uint32_t paint_local(void)
    _ensures(return == UINT32_MAX)
{
    struct sample s;
    memset(&s, 0xFF, sizeof(s));
    _assert(s.wide == -1);
    return s.narrow;
}

int64_t repaint_local(void)
    _ensures(return == 0x5A5A5A5A5A5A5A5A)
{
    struct sample s = {1, 2};
    memset(&s, 0x5A, sizeof(s));
    _assert(s.narrow == 0x5A5A5A5A);
    return s.wide;
}
