#include "pal.h"
#include <stdint.h>

/* Multiple labels in one function. PAL lowers a C label to Pulse's structured
   block-exit form `{ body } label L:;`, so each label needs a postcondition
   describing the ownership that survives the jump. */

void cleanup(void)
{
}

void unlock(void)
{
}

/* Single label: the case `test/goto_fail` already covers, kept here as the
   baseline that the multi-label cases below only differ from by degree. */
int32_t one_label(int32_t x)
{
    int32_t err = 0;
    if (x < 0)
        goto out;
    err = 1;
out: _ensures(_live(err) && _live(x))
    return err;
}

int32_t nested_goto(int32_t x)
    _ensures(return == (x < 0 ? 7 : 9))
{
    int32_t result = 7;
    if (x > 0)
        result = 8;
    else if (x < 0)
        goto out;
    result = 9;
out: _ensures(_live(result))
    return result;
}

int32_t nested_return(int32_t x)
    _ensures(return == (x < 0 ? 7 : 9))
{
    int32_t result = 7;
    if (x > 0)
        result = 8;
    else if (x < 0)
        return result;
    result = 9;
    return result;
}

/* Two labels: the usual C cleanup ladder. `out_free` runs the cleanup and then
   falls through into `out`. */
int32_t two_labels(int32_t x)
{
    int32_t err = 0;
    if (x < 0)
        goto out;
    if (x == 0)
        goto out_free;
    err = 1;
    return err;
out_free: _ensures(_live(err) && _live(x))
    cleanup();
out: _ensures(_live(err) && _live(x))
    return err;
}

/* Three labels: a deeper ladder. Each rung falls through into the next. */
int32_t three_labels(int32_t x)
{
    int32_t err = 0;
    if (x < 0)
        goto out;
    if (x == 0)
        goto out_free;
    if (x == 1)
        goto out_unlock;
    err = 1;
    return err;
out_unlock: _ensures(_live(err) && _live(x))
    unlock();
out_free: _ensures(_live(err) && _live(x))
    cleanup();
out: _ensures(_live(err) && _live(x))
    return err;
}

uint32_t leave_loop(uint32_t n, uint32_t stop)
    _ensures(return == (stop < n ? stop : n))
{
    uint32_t i = 0;
    uint32_t result;
    while (i < n)
        _invariant(i <= n && i <= stop)
    {
        if (i == stop) {
            result = i;
            goto out;
        }
        i = i + 1;
    }
    result = i;
out: _ensures(_live(result))
    return result;
}

void loop_cleanup(uint32_t *p, uint32_t n)
    _ensures(*p == n)
{
    uint32_t i = 0;
    while (i < n)
        _invariant(i <= n)
    {
        if (i == 1) {
            goto out;
        }
        i = i + 1;
    }
out: _ensures(_live(i))
    *p = n;
}

uint32_t direct_loop_exit(uint32_t n)
    _ensures(return == (n > 0 ? 1 : 0))
{
    uint32_t result = 0;
    while (n > 0)
        _invariant(result == 0)
    {
        result = 1;
        goto out;
    }
out: _ensures(_live(result))
    return result;
}
