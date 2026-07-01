#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

/* do-while with user-named flag variable for first-iteration invariant */
uint32_t simple_do(uint32_t n)
    _requires(n >= 1 && n <= 100)
{
    uint32_t i = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(n) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
    {
        i = i + 1;
    } while (i < n);
    return i;
}

/* do-while(0): execute body exactly once (no flag needed) */
uint32_t run_once(uint32_t x)
    _requires(x <= 100)
{
    uint32_t r = 0;
    do
        _invariant(_live(r))
    {
        r = x;
    } while (0);
    return r;
}

/* do-while with break: search for a threshold */
uint32_t find_limit(uint32_t n, uint32_t limit)
    _requires(n >= 1 && n <= 100 && limit <= 100)
{
    uint32_t i = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(n) && _live(limit) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
        _ensures((_specint) i <= n)
    {
        if (i == limit) {
            break;
        }
        i = i + 1;
    } while (i < n);
    return i;
}

/* do-while with continue: skip even iterations */
uint32_t count_odd(uint32_t n)
    _requires(n >= 1 && n <= 100)
{
    uint32_t i = 0;
    uint32_t count = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(count) && _live(n) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
        _invariant((_specint) count <= i)
    {
        i = i + 1;
        if (i % 2 == 0) {
            continue;
        }
        count = count + 1;
    } while (i < n);
    return count;
}

/* do-while whose only `continue` binds to the *inner* while loop, so the outer
 * do-while body has no top-level `continue`. This exercises the clean do-while
 * desugaring (`bool cont = true; while (cont) { body; first = false;
 * cont = cond; }`) rather than the legacy fallback, while still proving that a
 * nested-loop `continue` is correctly excluded by the top-level scan. */
uint32_t nested_continue(uint32_t n)
    _requires(n >= 1 && n <= 100)
{
    uint32_t i = 0;
    do
        _do_while_first(first)
        _do_while_cond(cont)
        _invariant(_live(i) && _live(n) && _live(first) && _live(cont))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
    {
        uint32_t j = 0;
        while (j < 3)
            _invariant(_live(j))
            _invariant((_specint) j <= 3)
        {
            j = j + 1;
            if (j == 2) {
                continue;
            }
        }
        i = i + 1;
    } while (i < n);
    return i;
}

struct counter {
    int x;
};

/* f: increment the struct's field by 1 and return whether the new value is
 * still < 10. Its postcondition pins both the mutation and the returned flag,
 * which is what lets g_loop reason about the loop. */
bool f(struct counter *s)
    _requires(s->x >= 0 && s->x < 10)
    _ensures(s->x == _old(s->x) + 1)
    _ensures(return == (s->x < 10))
{
    s->x = s->x + 1;
    return s->x < 10;
}

/* g_loop: a do-while whose guard is the impure call `f(&s)`, with an empty body
 * (so it takes the clean desugaring path). Because the guard has side effects,
 * PAL omits the auto `cont == (first || cond)` linking invariant. Instead we
 * name the continuation flag with `_do_while_cond(cont)` and supply our own
 * *pure* linking invariant `cont == (s.x < 10)` (justified by f's
 * postcondition). At loop exit the solver knows `not cont`, which via that
 * invariant gives `s.x >= 10`; combined with `s.x <= 10` this proves the
 * struct's field is exactly 10 on termination. */
int g_loop(void)
    _ensures(return == 10)
{
    struct counter s = { .x = 0 };
    do
        _do_while_cond(cont)
        _do_while_first(first)
        _invariant(_live(s.x) && _live(cont) && _live(first))
        _invariant((_specint) s.x >= 0 && (_specint) s.x <= 10)
        _invariant(cont == ((_specint) s.x < 10))
    {
    } while (f(&s));
    return s.x;
}
