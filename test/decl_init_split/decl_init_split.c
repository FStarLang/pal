#include <assert.h>
#include "pal.h"
#include <stdint.h>

// Regression test for PAL Error 228:
//
//   Tactic failed
//   Allocating a mutable local variable expects an annotated post-condition
//
// Surfaced by `QuicSlidingWindowExtremumUpdateMin/UpdateMax` in
// `msquic-pal/src/core/sliding_window_extremum.c`, where a combined
// declaration-with-initializer `T x = expr;` inside an `if`-block —
// followed by a `while` loop later in the function body — fails to verify.
//
// PAL splits a combined `T x = expr;` into two sibling IR statements
// (`StmtT::Decl` + `StmtT::Assign`), which Pulse lowers to a bare
// `let mut x : T;` followed by `x := expr;`.  When such an `if`-block is
// not in tail position, Pulse cannot infer the conditional's
// post-condition and Error 228 fires on the `let mut`.
//
// Solution: PAL supports an `_ensures(...)` annotation on an `if`,
// written between the condition and the opening brace (mirroring the
// while-loop annotation syntax).  It lowers to a Pulse
// `if (cond) ensures <P> { ... } else { ... }`, giving the conditional
// the post-condition Pulse needs.  Here `_ensures(_live(size))` states
// that the (mutable) local backing `size` is still live after the block.


void triggers_bug(uint32_t size)
{
    if (size > 0)
        _ensures(_live(size))
    {
        uint32_t rear = size - 1;
     }

    assert (1);
}
