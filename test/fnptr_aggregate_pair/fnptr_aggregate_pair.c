#include "pal.h"
#include <stdint.h>

/* A local aggregate holding two code pointers, handed by address to a call.
   Each pointer's validity is seeded where the aggregate is built; the call
   launders them (what comes back is stated at the callee's fresh value), so
   they are put down at the end without naming the address. With two of them
   in context, `drop_is_valid _ _ _` cannot tell them apart: the pre and post
   it is seeded at must still be named. */

void on_init(int32_t x, int32_t *y) { }
void on_fini(int32_t x) { }

struct pair_ops {
    void (*init)(int32_t, int32_t *);
    void (*fini)(int32_t);
};

void take_ops(struct pair_ops *o);

void build_and_take(void)
{
    struct pair_ops o = { .init = &on_init, .fini = &on_fini };
    take_ops(&o);
}
