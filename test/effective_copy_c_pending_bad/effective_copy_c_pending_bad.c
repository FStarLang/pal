#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void copy_uninitialized_allocation(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    int destination;
    memcpy(&destination, p, sizeof destination);
    free(p);
}

void unsupported_pointer_copy(void)
{
    int *source = NULL;
    void *destination = malloc(16);
    if (!destination)
        return;
    memcpy(destination, &source, sizeof source);
    free(destination);
}

int read_uninitialized_copy(void)
{
    int source;
    int destination;
    memcpy(&destination, &source, sizeof destination);
    return destination;
}
