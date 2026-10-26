#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

uint32_t read_wrong_copied_type(void)
{
    float source = 3.5f;
    void *destination = malloc(sizeof source);
    if (!destination)
        return 0;
    memcpy((uint32_t *)destination, &source, sizeof source);
    uint32_t result = *(uint32_t *)destination;
    free(destination);
    return result;
}
