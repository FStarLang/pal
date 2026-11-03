#include "pal.h"
#include <stdint.h>
#include <string.h>

struct buffer {
    uint8_t bytes[5];
    int tag;
};

void overflow_field(struct buffer *s)
    _requires(_inline_pulse(pure (FStar.Int32.v $(s->tag) == 42)))
{
    memset(s->bytes, 0, sizeof(uint8_t) * 6);
}
