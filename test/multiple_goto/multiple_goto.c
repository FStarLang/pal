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
