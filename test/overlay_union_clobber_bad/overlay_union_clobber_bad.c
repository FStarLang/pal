#include "pal.h"
#include <stdint.h>

/* A layered request layout: three layers each see one object through
   their own type. GENERIC_REQUEST is the scheduler's, BASE_REQUEST the
   library's, MOUNT_REQUEST one request type's. */
typedef struct _GENERIC_COMMON { uint32_t State; int32_t Status; } GENERIC_COMMON;
typedef struct _GENERIC_REQUEST { uint8_t Parameters[32]; GENERIC_COMMON Common; } GENERIC_REQUEST;
typedef struct _BASE_COMMON { uint64_t Store; uint32_t ActivityId; } BASE_COMMON;
typedef struct _BASE_PARAMS { uint8_t Opaque[16]; BASE_COMMON Common; } BASE_PARAMS;
typedef union _overlay _BASE_REQUEST { BASE_PARAMS BaseParams; GENERIC_REQUEST Generic; } BASE_REQUEST;
typedef struct _MOUNT_PARAMS { uint64_t Context; uint32_t Sequence; } MOUNT_PARAMS;
typedef union _overlay _MOUNT_REQUEST
{
    MOUNT_PARAMS Params;
    BASE_REQUEST Base;
    GENERIC_REQUEST Generic;
} MOUNT_REQUEST;

/* Params.Sequence is bytes [8, 12) of the scheduler's parameter bytes, so
   this write is not independent of them. */
void Clobber(MOUNT_REQUEST* Request)
    _requires(Request->Generic._active)
    _ensures(Request->Generic.Parameters[8] == _old(Request->Generic.Parameters[8]))
{
    Request->Params.Sequence = 5u;
}
