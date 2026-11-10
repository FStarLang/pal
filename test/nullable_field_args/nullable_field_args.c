#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* The address of a field handed to an optional parameter. The field is opened
   for the call and closed again after it, so what the callee gives back under
   its guard has to come back out of the guard before the field is closed. */

typedef struct Point
{
    uint32_t x;
    uint32_t y;
} Point;

void opt_out(_nullable _out _refine(*this == 7) uint32_t* p);
uint32_t opt_in(_nullable const uint32_t* p);
void opt_two_in(_nullable const uint32_t* a, _nullable const uint32_t* b);
void opt_two_out(_nullable _out _refine(*this == 7) uint32_t* a,
                 _nullable _out _refine(*this == 7) uint32_t* b);

/* One field of an object the caller holds, as an optional output. */
void out_field(Point* s)
    _ensures(s->x == 7)
{
    opt_out(&s->x);
}

/* One field of a local still being filled. */
uint32_t out_local_field(void)
    _ensures(return == 7)
{
    Point p;

    opt_out(&p.x);
    p.y = 0;
    return p.x;
}

/* Two fields of one borrowed struct, as two optional inputs. */
void two_in(const Point* s)
{
    opt_two_in(&s->x, &s->y);
}

/* Two fields of one struct, as two optional outputs. */
void two_out(Point* s)
    _ensures(s->x == 7 && s->y == 7)
{
    opt_two_out(&s->x, &s->y);
}

/* A union member is the union's own address, focused on the arm. */
union U
{
    uint32_t m;
    uint64_t n;
};

uint32_t union_in(union U* u)
    _requires(_inline_pulse(pure (Union_U_m? $(*u))))
{
    uint32_t r;

    r = opt_in(&u->m);
    return r;
}

void union_out(union U* u)
{
    opt_out(&u->m);
}
