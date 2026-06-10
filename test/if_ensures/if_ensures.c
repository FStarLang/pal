#include <assert.h>
#include "pal.h"
#include <stdint.h>



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

void if_while(uint32_t size)
{
    if (size > 0)
        _ensures(_live(size))
    {
        uint32_t rear = size - 1;
    }
    while (size > 0) {
        assert(1);
        
    }
}