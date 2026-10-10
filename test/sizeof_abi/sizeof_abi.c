#include "pal.h"

#include <stdint.h>

//
// Every `sizeof` of a record type resolves to the size clang computed for it
// under the target ABI, so arithmetic over record sizes has known bounds.
//

typedef struct _PAIR
{
    uint32_t First;
    uint32_t Second;
} PAIR;

typedef union _EITHER
{
    uint32_t AsWord;
    uint8_t AsBytes[4];
} EITHER;

typedef struct _OUTER
{
    PAIR Pair;
    EITHER Either;
    uint64_t Tag;
} OUTER;

void
SizesAreKnown(void)
{
    _assert(sizeof(PAIR) == 8);
    _assert(sizeof(EITHER) == 4);
    _assert(sizeof(OUTER) == 24);

    //
    // The point of pinning the sizes: a sum of them is statically in range,
    // which an opaque size would leave unprovable.
    //
    _assert(sizeof(PAIR) + sizeof(EITHER) + sizeof(OUTER) == 36);
}
