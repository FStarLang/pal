#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* A character store defines only the byte it writes: its neighbour in the
   same allocation is still indeterminate, and reading it is rejected. */
uint8_t read_unwritten_byte(void)
{
    void *p = malloc(2);
    if (!p)
        return 0;
    _array unsigned char *c = p;
    c[0] = 5;
    uint8_t r = c[1];
    free(p);
    return r;
}
