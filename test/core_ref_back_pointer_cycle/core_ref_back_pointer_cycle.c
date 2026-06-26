// Regression test: a struct that holds a `_core_ref` back-pointer to its parent
// can be embedded BY VALUE in that parent.
//
// The forward declaration `struct bar;` pins `bar` ahead of `inner` in the IR,
// and `inner`'s `_core_ref struct bar*` field used to be recorded as a
// dependency of `inner` on `bar`. Together with `bar`'s real by-value
// dependency on `inner`, that formed a cycle, so the declaration toposort fell
// back to source order and emitted `bar` before `inner`. `struct_bar__pred`
// then under-applied the 3-arity `struct_inner__pred` (omitting the spec
// argument), producing an ill-typed Struct_bar.fst.
//
// `collect_type_refs` now ignores `core_ref` pointers (they carry no predicate
// dependency), so `inner` sorts before `bar` and the embedded predicate is
// applied with its spec argument.

#include "pal.h"

struct bar;

struct inner {
    int *a;                       // owned field -> inner's spec is non-empty (3-arity pred)
    _core_ref struct bar *back;   // non-owning back-pointer -> dropped from inner's spec
};

struct bar {
    long *other;          // owned field -> bar's pred is non-empty (3-arity)
    struct inner myinner; // BY-VALUE embed of the cyclic struct
};
