// Test: the scope a `_refine` on a parameter is resolved in.
//
// A `_refine` sits inside a *parameter's type*, and says something about that
// parameter -- `this` -- in terms of the rest of the signature. Two things have
// to be true for that to be usable, and neither was:
//
//   1. it may name an *earlier parameter*, which is how an output's contract
//      says what it was computed from. A function-level `_ensures` cannot
//      always be used instead: it would have to dereference the output
//      pointer, and for a guarded (optional) output the `pts_to` is not
//      available there at all.
//
//   2. when a declaration carries the refinement and the definition names its
//      parameters differently -- which C allows, and which real headers do --
//      the refinement has to be read in the *definition's* scope, after the
//      two have been reconciled.

#include "pal.h"
#include <stdint.h>

// (1) `Dst`'s refinement names `Src`, a parameter declared before it. Before
// this change every parameter type was elaborated in the environment the
// function started with, so `Src` was simply not in scope here.
void copy_one(
    const uint32_t* Src,
    _out _refine(*this == *Src) uint32_t* Dst)
{
    *Dst = *Src;
}

// The refinement is a real proof obligation, not decoration: this one has to
// establish a computed relation to the earlier parameter.
void double_one(
    const uint32_t* Src,
    _out _refine(*this == *Src + *Src) uint32_t* Dst)
  _requires(*Src < 1000)
{
    *Dst = *Src + *Src;
}

// A refinement may name more than one earlier parameter.
void sum_two(
    const uint32_t* A,
    const uint32_t* B,
    _out _refine(*this == *A + *B) uint32_t* Dst)
  _requires(*A < 1000 && *B < 1000)
{
    *Dst = *A + *B;
}

// (2) The declaration names the parameters `Source`/`Target` and carries the
// refinement; the definition below names the very same parameters `from`/`to`.
// The refinement mentions `Source`, which the definition does not bind, so it
// only makes sense once `merge` has mapped the declaration's names onto the
// definition's -- and the scope check has to run after that, or it rejects a
// name that is legitimately not yet resolvable.
void copy_renamed(
    const uint32_t* Source,
    _out _refine(*this == *Source) uint32_t* Target);

// The definition repeats the declaration's annotations verbatim -- what SAL's
// _Use_decl_annotations_ does -- so the refinement still says `Source` while
// the definition binds `from`. Until `merge` has reconciled the two there is no
// answer to "is `Source` in scope here", which is why the scope check runs
// after it rather than before.
void copy_renamed(
    const uint32_t* from,
    _out _refine(*this == *Source) uint32_t* to)
{
    *to = *from;
}

// The same disagreement, but with the refinement written only on the
// declaration and the definition left bare -- the more natural spelling of the
// two, and the one a header/implementation split actually produces. The
// refinement still has to end up resolved against `src`/`dst`.
void copy_decl_only(
    const uint32_t* Source,
    _out _refine(*this == *Source) uint32_t* Target);

void copy_decl_only(const uint32_t* src, uint32_t* dst)
{
    *dst = *src;
}

// A caller sees the refinement as a postcondition on the output.
void use_copy(const uint32_t* src, _out uint32_t* dst)
  _ensures(*dst == *src)
{
    copy_one(src, dst);
}
