#include "pal.h"

// FEATURE: a struct whose FIRST FIELD is a common-initial-sequence (CIS) union.
// The union has exactly two byte-identical arms -- one anonymous, one named:
//
//     union {
//         struct { int a; int b; };   // anonymous arm: h->a / h->b
//         struct list list;           // named, tagged arm: h->list.a / h->list.b
//     };
//
// PAL collapses such a CIS union to a struct holding only the named arm, and
// rewrites every access through the anonymous arm (`h->a`) to go through the
// named arm (`h->list.a`). The two arms therefore denote the same storage, in
// bodies AND in specs (_requires / _ensures / assert).

struct list { int a; int b; };

struct head {
    union {
        struct { int a; int b; };   // anonymous arm  -> h->a / h->b
        struct list list;           // named, tagged arm -> h->list.a / h->list.b
    };
    int qlen;
};

// Write through the anonymous arm, read back through the named arm.
int write_anon_read_named(struct head *h, int v)
    _ensures(return == v)
{
    h->a = v;
    return h->list.a;
}

// Write through the named arm, read back through the anonymous arm.
int write_named_read_anon(struct head *h, int v)
    _ensures(return == v)
{
    h->list.a = v;
    return h->a;
}

// -------------------------------------------------------------------------
// Accessing a CIS union arm inside a spec (_requires / _ensures).
//
// In a function body clang resolves `h->a` / `h->list.a` through the anonymous
// union (IndirectFieldDecl). In a spec the access is parsed by PAL's own parser
// into a flat member chain; elab resolves it through the anonymous union and
// elim_cis then collapses it onto the named arm.

// (a) Anonymous first arm (`h->a`) in a _requires.
int spec_first_arm(struct head *h, int v)
    _requires(h->a == v)
    _ensures(return == v)
{
    return h->a;
}

// (b) Anonymous first arm (`h->a`) in an _ensures.
int spec_first_arm_ensures(struct head *h, int v)
    _ensures(h->a == return)
{
    h->a = v;
    return v;
}

// (c) Named arm (`h->list.a`) in a _requires.
int spec_named_arm(struct head *h, int v)
    _requires(h->list.a == v)
    _ensures(return == v)
{
    return h->list.a;
}

// (d) Named arm (`h->list.a`) in an _ensures.
int spec_named_arm_ensures(struct head *h, int v)
    _ensures(h->list.a == return)
{
    h->list.a = v;
    return v;
}
