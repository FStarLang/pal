// Test: `_container_of` round-trips through a (named) union. Every union
// member lives at offset 0, so PAL emits a `..._container` inverse (plus the
// round-trip lemmas and a null-preservation axiom) for every arm, just like
// for struct fields. Recovering the union from a member pointer yields the
// same address and does not touch ownership or the active arm.
//
// Note: forming `&u->arm` itself requires `arm` to be the active member.

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
// side), and the body reads the active arm through the recovered pointer.
int32_t read_via_member(_plain int32_t *p)
    _preserves(_inline_pulse(
      exists* (uv: $type(Payload)).
        pts_to $(_container_of(p, Payload, number)) #1.0R uv **
        Union_Payload.union_payload__pred
          (!$(_container_of(p, Payload, number))) 1.0R))
    _requires(_container_of(p, Payload, number)->number._active)
    _ensures(_container_of(p, Payload, number)->number._active)
    _ensures(return == _container_of(p, Payload, number)->number)
{
    Payload *u = _container_of(p, Payload, number);
    return u->number;
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
