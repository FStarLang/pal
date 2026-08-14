#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/*
 * `offsetof(S, m)` is a ground fact about the ABI, the same kind of fact as the
 * size of a complete record, and clang has already computed it. A back-patching
 * writer -- one that goes back and fills in a length or a checksum after the
 * rest of the structure is on media -- addresses the field it is rewriting this
 * way, so without it those functions cannot be translated at all.
 */

typedef struct
{
    uint32_t Magic;
    uint32_t CbSize;
} HEADER;

typedef struct
{
    HEADER BaseHeader;
    uint64_t Payload;
} RECORD;

size_t
header_cb_size_offset(void)
{
    return offsetof(RECORD, BaseHeader.CbSize);
}

size_t
payload_offset(void)
{
    return offsetof(RECORD, Payload);
}
