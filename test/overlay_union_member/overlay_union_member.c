#include "pal.h"
#include <stdint.h>

/* A tagged (non-overlay) union with an _overlay union member, as a request
   type that is also viewable as the generic request. An overlay union's
   value is its bytes, so there is no whole-value write for it, and the outer
   union has none either; its members are still written field by field. */
typedef struct _GENERIC_REQUEST { uint64_t Context; uint32_t Status; } GENERIC_REQUEST;
typedef struct _BASE_PARAMS { uint32_t Store; uint32_t Sequence; } BASE_PARAMS;
typedef union _overlay _BASE_REQUEST { BASE_PARAMS Params; GENERIC_REQUEST Generic; } BASE_REQUEST;
typedef struct _FLUSH_PARAMS { uint32_t Flags; } FLUSH_PARAMS;
typedef union _FLUSH_REQUEST
{
    FLUSH_PARAMS Params;
    BASE_REQUEST Base;
} FLUSH_REQUEST;

/* A struct holding the outer union holds an overlay, so it too is written
   field by field. */
typedef struct _HOLDER { uint32_t Tag; FLUSH_REQUEST Request; } HOLDER;

void Flush_SetFlags(FLUSH_REQUEST* Request, uint32_t Flags)
    _requires(Request->Params._active)
    _ensures(Request->Params._active && Request->Params.Flags == Flags)
{
    Request->Params.Flags = Flags;
}

void Holder_SetTag(HOLDER* Holder, uint32_t Tag)
    _ensures(Holder->Tag == Tag)
{
    Holder->Tag = Tag;
}
