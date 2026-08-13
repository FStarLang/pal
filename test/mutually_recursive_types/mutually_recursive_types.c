// Regression test: mutually recursive C types are broken automatically.
//
// C lets a type refer to another type that refers back to it, because a
// pointer only needs a forward declaration. The generated F* has no such
// escape hatch: each type gets its own module, and a struct's ownership
// predicate recurses through its pointer fields into the pointee's predicate.
// A cycle in the C types therefore becomes an F* module cycle, which F*
// rejects with `Error 308: Recursive dependency` while computing dependencies
// for the *whole* translation unit — so one recursive type in a third-party
// header used to take every other module down with it.
//
// `_core_ref` is the existing answer, but it has to be written in the source,
// which is not an option for headers we do not own. The merge pass now applies
// it automatically, and only to the pointers that actually close a cycle.
//
// Covers:
//   1. A two-struct pointer cycle (`peer` <-> `link`).
//   2. A cycle closed through a function-pointer typedef (`vtable` <-> `obj`),
//      which only exists because emission names the signature's types.
//   3. A cycle closed through an intermediate by-value embedding
//      (`outer` -> `middle` (by value) -> `outer`).
//   4. A self-referential struct is NOT broken: it stays in one module, so it
//      keeps its typed pointer and its automatic ownership.
//   5. Fields outside the cycle keep their ordinary typed model.

#include "pal.h"
#include <stdint.h>

/* 1. Direct two-struct cycle. Each side's back-pointer becomes a core_ref. */
struct link;

struct peer {
    int32_t peer_id;
    struct link *first_link;
};

struct link {
    int32_t weight;
    struct peer *owner;
};

/* 2. Cycle through a function-pointer typedef: `obj` stores a `vtable`, whose
 *    signature mentions `obj *`. */
struct obj;
typedef int32_t (*vtable)(struct obj *self);

struct obj {
    int32_t tag;
    vtable dispatch;
};

/* 3. Cycle closed through a by-value embedding: `outer` embeds `middle`, which
 *    points back at `outer`. Only the pointer can be broken. */
struct outer;

struct middle {
    struct outer *up;
};

struct outer {
    int32_t depth;
    struct middle mid;
};

/* 4. A self-referential struct is left alone: `Struct_selfnode` referring to
 *    `Struct_selfnode` is not a module cycle. */
typedef struct selfnode {
    int32_t data;
    _plain struct selfnode *next;
} selfnode;

/* 5. Non-cycle fields keep their typed model, so ordinary reads still work. */
int32_t peer_id_of(const struct peer *p) {
    return p->peer_id;
}

int32_t weight_of(const struct link *l) {
    return l->weight;
}

int32_t tag_of(const struct obj *o) {
    return o->tag;
}

int32_t depth_of(const struct outer *o) {
    return o->depth;
}

/* 4 (continued). The self-pointer keeps its typed model. This only elaborates
 *    if `struct selfnode`'s `next` field is still a `ref struct selfnode`; had
 *    the pass broken the self-loop it would be an untyped `core_ref`. */
_include_pulse(Mutually_recursive_types_include1,
  let next_of (n: $type(selfnode)) : $type(selfnode *) = n.$field(selfnode::next)
)
