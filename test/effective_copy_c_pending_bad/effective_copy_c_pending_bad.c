#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void copy_prepared(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    _ghost_stmt($prepare(int) $(p));
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

void incompatible_prepared_copy(void)
{
    float source = 3.5f;
    void *destination = malloc(16);
    if (!destination)
        return;
    _ghost_stmt($prepare(int) $(destination));
    memcpy(destination, &source, sizeof source);
    free(destination);
}
