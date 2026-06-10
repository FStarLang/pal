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


// Minimal case: a single declaration-with-initializer local inside an `if`.
void single_local(uint32_t size)
{
    if (size > 0)
        _ensures(_live(size))
    {
        uint32_t rear = size - 1;
     }

    assert (1);
}

// Several local declarations-with-initializer inside one `if`-block.
void multiple_locals(uint32_t size)
{
    if (size > 0)
        _ensures(_live(size))
    {
        uint32_t rear = size - 1;
        uint32_t next = rear;
        uint32_t sum = next;
    }

    assert (1);
}

// `if`/`else` pattern: both branches declare-and-write a local.  The single
// `_ensures` on the `if` describes the post-condition of the whole
// conditional, so it covers both branches.
void if_else_locals(uint32_t size)
{
    if (size > 0)
        _ensures(_live(size))
    {
        uint32_t hi = size - 1;
    } else {
        uint32_t lo = size + 1;
    }

    assert (1);
}

// Writing to a local declared *before* the `if`, alongside a fresh local
// inside the block.  The outer local stays live afterwards, so the
// post-condition mentions it as well (slprops are combined with `&&`).
void write_outer_local(uint32_t size)
{
    uint32_t total = 0;

    if (size > 0)
        _ensures(_live(size) && _live(total))
    {
        uint32_t delta = size - 1;
        total = total + delta;
    }

    assert (1);
}

// Shadowing: a local named `v` is declared independently in the `if` branch,
// the `else` branch, and the enclosing scope, and used differently in each.
// The inner declarations shadow the outer `v` only within their own branch,
// so after the conditional `v` must still resolve to the outer local (read by
// the trailing assert).  Exercises that PAL keeps these scopes distinct.
void shadowed_local(uint32_t size)
{
    uint32_t v = 7;

    if (size > 0)
        _ensures(_live(size) && _live(v))
    {
        uint32_t v = size - 1;
        uint32_t lower = v;
    } else {
        uint32_t v = size + 1;
        uint32_t higher = v;
    }

    assert (v >= 0);
}
