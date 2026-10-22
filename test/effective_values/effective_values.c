#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct effective_pair { uint32_t a; uint32_t b; };
union effective_union { uint32_t i; float f; };

uint32_t struct_field(struct effective_pair *p)
    _ensures(return == p->b)
{
    return p->b;
}

uint32_t array_element(void)
    _ensures(return == 2)
{
    uint32_t a[2] = { 1, 2 };
    return a[1];
}

float union_member(void)
{
    union effective_union u;
    u.f = 1.0f;
    float r = u.f;
    return r;
}

uint8_t character_store(void)
    _ensures(return == 5)
{
    uint8_t *p = malloc(sizeof *p);
    if (!p)
        return 5;
    *p = 5;
    uint8_t r = *p;
    free(p);
    return r;
}
