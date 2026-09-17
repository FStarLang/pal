#include "pal.h"
#include <stdint.h>

// Regression test: a struct tag whose FIRST mention is inside a pointer field,
// with no file-scope forward declaration.
//
// `struct opaque_fwd;` below is declared before use and has always worked: PAL
// emits an axiomatized placeholder module for it (`assume val struct_... :
// Type0`, plus its predicates), which is the right treatment for a type this
// translation unit never sees the definition of.
//
// `struct opaque_implicit` is the same situation as far as C is concerned --
// an incomplete type used only through a pointer -- but the tag is introduced
// implicitly by its use inside `holder`. PAL used to report
//
//     error: (internal, after merge) unknown struct opaque_implicit
//
// and then emit Struct_holder.fst REFERENCING `Struct_opaque_implicit.…`
// anyway. The module was never emitted, so every consumer failed downstream
// with `Error 72: Module name Struct_opaque_implicit could not be resolved`,
// which reads like a proof failure and is not one.
//
// This is not a corner case: SDK headers declare plenty of such pointers
// (FunOS's `struct per_lport_stats *perlport_stats` in vplocal.h is one), and
// in the cocovisor it accounted for the single largest bucket of failures.
//
// The fix synthesizes the same placeholder the explicit case already gets, so
// both fields below translate identically.

struct opaque_fwd;

struct holder {
    int tag;
    struct opaque_fwd *a;      // explicit forward declaration -- always worked
    struct opaque_implicit *b; // tag introduced implicitly, right here
};

// Reads a normal field of the struct that carries the two opaque pointers.
// The spec is deliberately minimal: what is under test is that both opaque
// tags get a module, not anything about this function.
int get_tag(struct holder *h)
{
    return h->tag;
}

// Both opaque types also appear in function SIGNATURES, to confirm that a
// `ref Struct_<tag>.struct_<tag>` resolves for the implicit spelling exactly as
// it does for the explicit one. They are parameters rather than return values
// on purpose: returning an owned pointer out of a struct raises an ownership
// obligation that has nothing to do with this test, and raises it identically
// for both spellings.
int takes_fwd(struct opaque_fwd *a, int x)
{
    return x;
}

int takes_implicit(struct opaque_implicit *b, int x)
{
    return x;
}
