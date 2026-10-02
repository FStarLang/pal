// Test: preliminary support for mutually-recursive structs via `_core_ref`.
//
// `struct parent` owns a `child`; `struct child` holds a NON-owning back-pointer
// to its parent, annotated `_core_ref`.
//
// Without `_core_ref`, PAL emits two F* modules (Struct_parent / Struct_child)
// that reference each other, which F* rejects as a cyclic module dependency
// (Error 308); the auto-generated ownership predicates would also recurse
// forever. Translating the back-pointer as an axiomatized `core_ref` drops
// `parent` from `child`'s F* type and emits no automatic ownership for it,
// breaking both the module cycle and the non-terminating predicate.
//
// Palow needs none of that. A pointer field's F* type is `ptr` whatever it
// points at, so the two type declarations are already acyclic and neither
// module has to mention the other. What is left is the *ownership* cycle --
// parent owning child owning parent -- and that is a fact about the C, not
// about the model: the back-pointer is non-owning, which is exactly what
// `_plain` says. So Palow spells the same program with an annotation it
// already has, and `_core_ref` disappears.

#include "pal.h"
#include <stddef.h>
#include <stdbool.h>

struct parent;

struct child {
    int data;
#ifdef PALOW
    struct parent *_plain up; // non-owning back-pointer
#else
    _core_ref struct parent *up; // non-owning back-pointer (breaks the cycle)
#endif
};

struct parent {
    int tag;
    struct child *down; // owning pointer to the child
};

/* Demonstrates the intended use of `core_ref`: a hand-written ownership
 * predicate over the cyclic parent/child structure. The parent owns its child
 * via `down`; the child's raw `up` back-pointer is recovered as a typed
 * `ref parent` with `core_to_ref` and asserted to point back to the parent.
 * This is exactly the reasoning that the auto-generated (acyclic) predicates
 * cannot express, and that `core_ref` enables the user to write by hand. */
#ifdef PALOW
// The same hand-written predicate in Palow. There is nothing to recover: the
// back-pointer already *is* a `ptr`, the same type `p` has, so the last
// conjunct is a plain equation rather than a round trip through `core_to_ref`.
_include_pulse(Core_ref_struct_include,
  let is_node (p: $type(struct parent *)) (pv: $type(struct parent)) (cv: $type(struct child)) : slprop =
    Struct_parent.struct_parent_pts_to p 1.0R pv **
    Struct_child.struct_child_pts_to pv.$field(struct parent::down) 1.0R cv **
    pure (cv.$field(struct child::up) == p)
)
#else
_include_pulse(Core_ref_struct_include,
  let is_node (p: $type(struct parent *)) (pv: $type(struct parent)) (cv: $type(struct child)) : slprop =
    pts_to p pv **
    pts_to pv.$field(struct parent::down) cv **
    pure (Pulse.Lib.C.CoreRef.core_to_ref $type(struct parent) cv.$field(struct child::up) == p)
)
#endif

/* Field write on the struct that holds the core_ref. */
void set_data(struct child *c, int v) {
    c->data = v;
}

/* Field read on the struct that holds the core_ref. */
int get_data(struct child *c) {
    return c->data;
}

/* Read the raw back-pointer and test it for null. Exercises the core_ref
 * null/equality machinery (core_is_null). */
bool has_parent(struct child *c) {
    return c->up != NULL;
}
