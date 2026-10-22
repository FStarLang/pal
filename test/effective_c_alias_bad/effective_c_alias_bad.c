#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

float read_incompatible(void)
{
    void *p = malloc(16);
    if (!p)
        return 0.0f;
    *(int *)p = 7;
    float result = *(float *)p;
    free(p);
    return result;
}

/* A copy gives allocated storage the source's type, here `float`. */
int read_copied_incompatible(void)
{
    float source = 3.5f;
    void *destination = malloc(16);
    if (!destination)
        return 0;
    memcpy(destination, &source, sizeof source);
    int result = *(int *)destination;
    free(destination);
    return result;
}
