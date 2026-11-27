#pragma once
#include "pal.h"
#include <stdint.h>

/* The anonymous member differs between the two translation units. Spelling
   its type independently of the include path must not make them agree. */
typedef struct _shared_rec {
#ifdef WIDE_MEMBER
    union { uint64_t a; uint8_t b; };
#else
    union { uint32_t a; uint8_t b; };
#endif
} shared_rec;
