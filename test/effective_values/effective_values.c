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

/* A character store into untyped storage installs no effective type
   (6.5p6): the byte is defined, and the storage stays raw. */
uint8_t character_store(void)
    _ensures(return == 5)
{
    void *p = malloc(1);
    if (!p)
        return 5;
    *(unsigned char *)p = 5;
    uint8_t r = *(unsigned char *)p;
    free(p);
    return r;
}
