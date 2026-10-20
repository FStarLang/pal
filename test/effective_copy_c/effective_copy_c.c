#include "pal.h"
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

int copy_initialized(void)
    _ensures(return == 37)
{
    int source = 37;
    int target;
    memcpy(&target, &source, sizeof target);
    return target;
}

void copy_uninitialized(void)
{
    int source;
    int target;
    memcpy(&target, &source, sizeof target);
}

uint32_t copy_representation(void)
{
    float source = 3.5f;
    uint32_t target;
    memcpy(&target, &source, sizeof target);
    return target;
}

int copy_into_allocated(void)
    _ensures(return == 0 || return == 37)
{
    int source = 37;
    void *target = malloc(16);
    if (!target)
        return 0;
    memcpy(target, &source, sizeof source);
    int result = *(int *)target;
    free(target);
    return result;
}

int copy_into_prepared(void)
    _ensures(return == 0 || return == 37)
{
    int source = 37;
    void *target = malloc(16);
    if (!target)
        return 0;
    _ghost_stmt($prepare(int) $(target));
    memcpy(target, &source, sizeof source);
    int result = *(int *)target;
    free(target);
    return result;
}

int copy_into_prepared_typed_allocation(void)
    _ensures(return == 0 || return == 37)
{
    int source = 37;
    int *target = malloc(sizeof *target);
    if (!target)
        return 0;
    _ghost_stmt($prepare(int) $(target));
    memcpy(target, &source, sizeof source);
    int result = *target;
    free(target);
    return result;
}

float copy_type_comes_from_source(void)
{
    float source = 3.5f;
    void *target = malloc(sizeof source);
    if (!target)
        return 0.0f;
    memcpy((uint32_t *)target, &source, sizeof source);
    float result = *(float *)target;
    free(target);
    return result;
}
