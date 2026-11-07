#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

struct __attribute__((aligned(16))) aligned_record {
    uint32_t value;
};

_allocated void *word_allocate(size_t size)
    _ensures(_inline_pulse(
        mem_pts_to_at $(return) 1.0R (uninit (FStar.SizeT.v $(size)))
          (Seq.create (FStar.SizeT.v $(size)) None) **
        freeable $(return) $(size) **
        pure (aligned $(return) 8sz /\ allocated_region $(return) (FStar.SizeT.v $(size)))));

void insufficient_alignment(void)
{
    struct aligned_record *p = word_allocate(sizeof(*p));
    p->value = 42;
    free(p);
}
