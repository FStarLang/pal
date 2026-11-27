#pragma once
#include "pal.h"
#include <stdint.h>

/* A named record with two anonymous members. Clang spells an anonymous
   member's type with its source location; that spelling must not depend on
   the path through which the header was included. */
typedef struct _shared_rec {
    union { uint32_t a; uint16_t b; };
    union { uint64_t c; uint8_t d; };
} shared_rec;

int rec_first(_plain shared_rec *r);
