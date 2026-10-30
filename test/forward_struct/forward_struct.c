#include "pal.h"

// Forward declaration only — opaque type
struct opaque;

// Forward declaration with later definition
struct point;

struct point {
    int x;
    int y;
};

typedef struct opaque opaque;

void use_point(struct point *p) {
    p->x = 1;
    p->y = 2;
}

struct opaque *use_opaque(_consumes opaque *o) {
    return o;
}

/* The back pointer is cyclic; the by-value member still has to come first. */
struct owner;

struct observer {
    struct owner *target;
};

struct owner_member {
    struct owner *parent;
    unsigned value;
};

struct owner {
    struct owner_member member;
};

unsigned owner_value(const struct owner *p)
    _ensures(return == p->member.value)
{
    return p->member.value;
}

void set_owner_value(struct owner *p, unsigned value)
    _ensures(p->member.value == value)
    _ensures(p->member.parent == _old(p->member.parent))
{
    p->member.value = value;
}

unsigned observer_value(const struct observer *p)
    _ensures(return == p->target->member.value)
{
    return p->target->member.value;
}

struct tagged_owner;

struct tagged_member {
    struct tagged_owner *parent;
    unsigned value;
};

union tagged_contents {
    struct tagged_member member;
    unsigned raw;
};

struct tagged_owner {
    union tagged_contents contents;
};

unsigned tagged_owner_value(const struct tagged_owner *p)
    _requires(p->contents.member._active)
    _ensures(return == p->contents.member.value)
{
    return p->contents.member.value;
}
