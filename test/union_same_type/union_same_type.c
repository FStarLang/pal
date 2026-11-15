#include "pal.h"
#include <stdint.h>

/* An overlay union whose members are all one integer type is that integer:
   a field renamed with the old name kept for readers. Any member reads what
   any member wrote, with nothing to say about which one is active. */

typedef uint64_t drive_id;

struct info {
    uint32_t kind;
    union _overlay {
        drive_id id;
        drive_id number; /* the old name */
    };
};

drive_id get_number(const struct info *i)
    _ensures(return == i->id)
{
    return i->number;
}

drive_id set_then_get(struct info *i, drive_id v)
    _ensures(return == v)
    _ensures(i->id == v)
{
    i->id = v;
    return i->number;
}

struct info make(drive_id v)
    _ensures(return.number == v)
{
    struct info i = { .kind = 1, .id = v };
    return i;
}

drive_id via_arm(struct info *i)
    _requires(i->number._active)
    _ensures(return == i->id)
{
    return get_number(i);
}

union _overlay named {
    uint32_t a;
    uint32_t b;
};

uint32_t named_local(uint32_t x)
    _ensures(return == x)
{
    union named n;
    n.a = x;
    return n.b;
}

uint32_t named_init(void)
    _ensures(return == 0)
{
    union named n = {0};
    return n.b;
}
