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

// (3) The same refinements, but on a *regular* (non-`_out`) parameter. An
// `_out` pointee is uninitialized on entry and initialized on return, so its
// refinement is a guarantee only -- it lands in `ensures` alone. A plain
// pointer's pointee is initialized on both sides, so the very same annotation
// is an *obligation on the caller* as well as a guarantee on return, and has to
// be emitted into `requires` and `ensures` both.
//
// Nothing in this body re-establishes the relation, so it verifies only if the
// refinement is assumed on entry -- which is the `requires` half.
void keep_equal(
    const uint32_t* Src,
    _refine(*this == *Src) uint32_t* Both)
{
}

// Both halves at once, and neither is redundant: the body perturbs `Src` and
// `Both`, so the entry refinement is what says they started equal, and the exit
// refinement is a real obligation about the values they end at.
void bump_together(
    uint32_t* Src,
    _refine(*this == *Src) uint32_t* Both)
  _requires(*Src < 1000)
{
    *Src = *Src + 1;
    *Both = *Both + 1;
}

// The declaration/definition rename of (2), on a regular parameter: the
// refinement naming `Source` has to be resolved against `from` after `merge`,
// and then appear on both sides of the spec.
void keep_equal_renamed(
    const uint32_t* Source,
    _refine(*this == *Source) uint32_t* Target);

void keep_equal_renamed(const uint32_t* from, uint32_t* to)
{
    *to = *from;
}

// The caller's side of the same coin, and the reason both halves have to be
// emitted: the `_requires` here is what *discharges* the refinement at the call
// (an `_out` refinement never asks this), and the `_ensures` is provable only
// from the refinement coming back out, since the call havocs `*both`.
void use_keep_equal(const uint32_t* src, uint32_t* both)
  _requires(*both == *src)
  _ensures(*both == *src)
{
    keep_equal(src, both);
}

// The same, where the values genuinely change across the call: the caller keeps
// no handle on what `bump_together` wrote, so the relation it learns about the
// new values can only have come from the refinement's `ensures` half.
void use_bump_together(uint32_t* a, uint32_t* b)
  _requires(*b == *a && *a < 1000)
  _ensures(*b == *a)
{
    bump_together(a, b);
}
