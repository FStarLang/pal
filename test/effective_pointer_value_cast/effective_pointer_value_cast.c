#include "pal.h"
#include <stdint.h>

typedef int int_alias;

void *to_void(int *p _plain) {
    return (void *)p;
}

int *from_void(void *p _plain) {
    return (int *)p;
}

float **cast_address(int **p _plain) {
    return (float **)p;
}

int_alias *read_same_type(int **p) {
    return *(int_alias **)p;
}

int *read_roundtrip(int **p) {
    return *(int **)(void *)p;
}

void accept_address(float **p _plain) {
}

void cast_address_argument(int **p _plain) {
    accept_address((float **)p);
}

int *call_roundtrip(int **p) {
    return read_same_type((int **)(void *)p);
}

_plain int **typed_identity(int **p _plain)
    _ensures(return == p)
{
    return p;
}

void returned_address_argument(int **p _plain) {
    accept_address(cast_address(p));
}

_plain float **unknown_address(void *p _plain) {
    if (p)
        return p;
    return p;
}

void unknown_return_address_argument(int **p _plain) {
    float **q = unknown_address(p);
    accept_address(q);
}

_plain int **identity_through_void(void *p _plain)
    _ensures((void *)return == p)
{
    return p;
}

_ghost_arg(int *v)
_preserves(_inline_pulse(ptr_pts_to $(p) 1.0R $(v)))
_plain int *read_returned_roundtrip(int **p _plain) {
    int **q = typed_identity(identity_through_void(p));
    _ghost_stmt(
        rewrite (ptr_pts_to $(p) 1.0R $(v))
            as (ptr_pts_to $(q) 1.0R $(v)));
    _plain int *result = *q;
    _ghost_stmt(
        rewrite (ptr_pts_to $(q) 1.0R $(v))
            as (ptr_pts_to $(p) 1.0R $(v)));
    return result;
}
