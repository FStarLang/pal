#include "pal.h"

// FEATURE: casting a struct whose FIRST FIELD is a common-initial-sequence
// (CIS) union to that union's NAMED arm pointer type. The union has an
// anonymous arm and a named, tagged arm with identical layout:
//
//     union {
//         struct { int a; int b; };   // anonymous arm: h->a / h->b
//         struct list list;           // named, tagged arm
//     };
//
// letting code read the members directly AND obtain a `struct list *` view of
// the leading pair via `(struct list *) h`.
//
// PAL support: the frontend lowers `(struct list *)h` to `&h->list` (the named
// arm is at offset 0), and elim_cis collapses the byte-identical CIS union so
// `struct list` becomes the leading member. The cast view thus aliases the CIS
// leading slot `h->a`. Each function writes `v` and reads it back -- crossing
// between the cast view and the anonymous arm -- so `_ensures(return == v)`
// proves the two denote the same storage.

struct list { int a; int b; };

struct head {
    union {
        struct { int a; int b; };   // anonymous arm  -> h->a / h->b
        struct list list;           // named, tagged arm -> h->list.a / &h->list
    };
    int qlen;
};

// Write through the cast pointer, read back through the anonymous arm.
int write_via_cast(struct head *h, int v)
    _ensures(return == v)
{
    struct list *l = (struct list *)h;
    l->a = v;
    return h->a;
}

// Write through the anonymous arm, read back through the cast pointer.
int read_via_cast(struct head *h, int v)
    _ensures(return == v)
{
    h->a = v;
    struct list *l = (struct list *)h;
    return l->a;
}

// Write and read entirely through the cast pointer.
int roundtrip_via_cast(struct head *h, int v)
    _ensures(return == v)
{
    struct list *l = (struct list *)h;
    l->a = v;
    return l->a;
}
