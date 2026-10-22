#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Zero bytes from calloc have no effective type, so neither does their copy
   (C11 6.5p6); an `int` read of the copy is then defined. */
int copy_untyped_then_read(void)
    _ensures(return == 0)
{
    void *s = calloc(1, sizeof(int));
    if (!s)
        return 0;
    void *d = malloc(sizeof(int));
    if (!d) {
        free(s);
        return 0;
    }
    memcpy(d, s, sizeof(int));
    int r = *(int *)d;
    free(d);
    free(s);
    return r;
}
