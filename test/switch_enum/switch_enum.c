#include "pal.h"
#include <stdint.h>

/* The switch condition is promoted to int by clang, but an enumeration is
 * modeled by its underlying integer type, so the promotion is the identity and
 * the scrutinee binding must keep the enumeration's own type. */
typedef enum { COLOR_RED = 0, COLOR_GREEN = 1, COLOR_BLUE = 2 } color;

struct pixel {
    color c;
    uint32_t v;
};

uint32_t weight(struct pixel *p)
    _requires(p->c == COLOR_RED || p->c == COLOR_GREEN || p->c == COLOR_BLUE)
    _ensures(return <= 3)
{
    switch (p->c) {
    case COLOR_RED:
        return 1;
    case COLOR_GREEN:
        return 2;
    default:
        return 3;
    }
}

uint32_t weight_local(color c)
    _ensures(return <= 3)
{
    uint32_t r;
    switch (c) {
    case COLOR_RED:
        r = 1;
        break;
    case COLOR_GREEN:
        r = 2;
        break;
    default:
        r = 3;
        break;
    }
    return r;
}
