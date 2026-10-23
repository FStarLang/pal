#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* malloc gives indeterminate bytes, so even a character read of one that was
   never written is rejected. */
uint8_t read_uninit_byte(void)
{
    void *p = malloc(1);
    if (!p)
        return 0;
    uint8_t r = *(unsigned char *)p;
    free(p);
    return r;
}
