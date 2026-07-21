#include "pal.h"
#include <stdint.h>

/*
 * Regression test: a union with an array-typed arm.
 *
 * PAL emits, for every non-bitfield union arm, an `activate_<arm>` ghost
 * axiom whose postcondition hands back ownership of the (now-active) arm's
 * storage. For a *scalar* arm the arm projects to `ref T`, so the emitted
 * `Pulse.Lib.Reference.pts_to_uninit (union__<arm> x)` is well-typed. For an
 * *array* arm the projection `union__<arm> x` has type `array T` (an array
 * handle, not a `ref`), so `Reference.pts_to_uninit` does not apply and F*
 * rejects the generated module (Error 12: expected ref, got array).
 *
 * The array arm therefore hands back a full `array_pts_to` over an
 * existential `full_array_lspec T n` of the arm's *static* length (mirroring
 * the arm's `aux_raw_unfold`), rather than an `array_pts_to_uninit'` that
 * hides the length. Pinning the length is what makes the postcondition usable:
 * an indexed write `a->arm[i] = ...` can then discharge `i < length`.
 *
 * `read_word` exercises the scalar arm; `write_bytes` activates the array arm
 * and writes every element, which only type-checks because the recovered
 * `array_pts_to` carries the known length 4.
 */

union addr {
    uint8_t  bytes[4];
    uint32_t word;
};

uint32_t read_word(union addr *a)
    _requires(a->word._active)
{
    return a->word;
}

// Activate the array arm, then write each element. The indexed writes are
// only well-typed because `$activate` recovers an `array_pts_to` of the
// arm's static length (4), so each `bytes[i]` is provably in bounds.
void write_bytes(union addr *a)
{
    _ghost_stmt($activate(union addr::bytes) $(a));
    a->bytes[0] = 1;
    a->bytes[1] = 2;
    a->bytes[2] = 3;
    a->bytes[3] = 4;
}
