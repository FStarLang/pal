#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct pair { uint64_t lo; uint64_t hi; };
struct box { uint64_t a; uint64_t b; };

_pure struct pair pair_of(struct box b) { return (struct pair){ b.a, b.b }; }

/*
 * An accessor that is a projection and nothing more. Saying so outright --
 * `return == E`, with `E` free of `return` -- is emitted as Pulse's
 * `rewrites_to`, which the prover reads as a substitution rather than as one
 * more equality to look up.
 */
struct pair get(const struct box *b) _ensures(return == pair_of(*b));

/*
 * Projects a call result twice, once inside a guarded branch. Two things have
 * to hold at once for this to check, and each guards a separate defect:
 *
 *   - the two call results must not share a name. Pulse's own hoisting numbers
 *     its temporaries from a counter that does not survive leaving a
 *     statement, so the branch-local one would capture the one bound before
 *     the branch and the branch postcondition would be ill-typed. PAL names
 *     them itself instead.
 *
 *   - the call's result must not survive into the branch postcondition. It is
 *     a branch-local binding, so it would be closed existentially, and Pulse's
 *     join gives up on an `exists*` and leaves a `match` nothing after the
 *     conditional can take a resource out of. `rewrites_to` rewrites it away
 *     before the branch ends.
 */
void fill(_out struct box *dst, const struct box *src, _nullable const struct box *opt)
    _ensures(dst->a == pair_of(*src).lo)
{
    _ghost_stmt($unfold-uninit(struct box) $(dst));
    dst->a = get(src).lo;

    if (opt != NULL)
    {
        dst->b = get(opt).lo;
    }
    else
    {
        dst->b = 0;
    }

    _ghost_stmt($fold(struct box) $(dst) _ _);
}
