#include "pal.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>

typedef int32_t (*callback)(int32_t);

struct handlers {
    uint32_t count;
    callback on_event;
};

struct outer {
    struct handlers inner;
    callback fallback;
};

// Zeroing an object with a function-pointer field leaves it null, as a
// brace-initialized or static one would be (C11 6.7.9p10).
void zero_handlers(struct handlers *h)
    _ensures(h->count == 0)
    _ensures(h->on_event == NULL)
{
    memset(h, 0, sizeof(struct handlers));
}

// The same through a nested struct.
void zero_outer(struct outer *o)
    _ensures(o->inner.on_event == NULL)
    _ensures(o->fallback == NULL)
{
    memset(o, 0, sizeof(*o));
}

// The null test a caller makes before dispatching sees the zero.
int32_t is_unset(struct handlers *h)
    _ensures(return == 1)
{
    memset(h, 0, sizeof(*h));
    callback cb = h->on_event;
    if (cb == NULL) {
        return 1;
    }
    return 0;
}
