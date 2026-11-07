// Test: `_container_of` round-trips through a (named) union. Every union
// member lives at offset 0, so recovering the union from a member pointer is
// the member pointer itself: no arithmetic, no ownership, and the active arm
// is untouched. NULL is preserved for the same reason.

#include "pal.h"
#include <stddef.h>
#include <stdint.h>

typedef union Payload {
    int32_t number;
    int32_t *pointer;
} Payload;

void roundtrip(Payload *u)
    _requires(u->number._active)
    _ensures(u->number._active)
{
    Payload *v = _container_of(&u->number, Payload, number);
    _assert(v == u);
}

void roundtrip_second_arm(Payload *u)
    _requires(u->pointer._active)
    _ensures(u->pointer._active)
{
    Payload *v = _container_of(&u->pointer, Payload, pointer);
    _assert(v == u);
}

// Ownership of the union is stated on the `_container_of` term itself (spec
// side). The recovered pointer is the member pointer, so focusing the union
// on its live arm through one hands out the member at the other.
int32_t read_via_member(_plain int32_t *p)
    _preserves(_inline_pulse(
      exists* (v: Int32.t).
        Union_Payload.union_Payload_pts_to $(_container_of(p, Payload, number)) 1.0R
          (Union_Payload.Union_Payload_number v)))
{
    Payload *u = _container_of(p, Payload, number);
    _ghost_stmt(Union_Payload.union_Payload_focus_number $(u));
    int32_t r = *p;
    _ghost_stmt(Union_Payload.union_Payload_unfocus_number $(u));
    return r;
}

struct holder {
    int32_t tag;
    Payload payload;
};

// `container_of` through a union nested in a struct.
void nested(struct holder *h)
    _requires(h->payload.number._active)
{
    int32_t *p = &h->payload.number;
    Payload *u = _container_of(p, Payload, number);
    struct holder *g = _container_of(u, struct holder, payload);
    _assert(g == h);
}

// Every union arm is at offset 0, so NULL is preserved.
void null_roundtrip(void)
{
    int32_t **p = NULL;
    Payload *v = _container_of(p, Payload, pointer);
    _assert(v == NULL);
}
