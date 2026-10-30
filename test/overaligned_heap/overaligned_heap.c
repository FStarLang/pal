#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

struct __attribute__((aligned(256))) overaligned_record {
    uint32_t value;
};

void initialize_heap(void)
{
    struct overaligned_record *p = malloc(sizeof(*p));
    if (p == NULL) {
        return;
    }
    p->value = 42;
    free(p);
}
