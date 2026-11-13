#include "pal.h"
#include <stdint.h>

/* An overlay request whose generic view is a member at offset 0, read
   through a const pointer by a callee. Lending the member out and taking it
   back unchanged writes its bytes back over themselves, which must leave
   the whole union -- including bytes only the other member names -- as it
   was. */
typedef struct _BASE { uint64_t Store; uint64_t Context; } BASE;
typedef struct _PARAMS { uint64_t Header[2]; uint32_t Index; uint32_t Count; } PARAMS;
typedef union _overlay _REQUEST { BASE Base; PARAMS Params; } REQUEST;

uint64_t Base_GetStore(const BASE* Base)
{
    return Base->Store;
}

uint64_t Request_GetStore(const REQUEST* Request)
    _requires(Request->Base._active && Request->Params._active)
    _requires(Request->Params.Index < Request->Params.Count)
    _ensures(Request->Params.Index < Request->Params.Count)
{
    return Base_GetStore(&Request->Base);
}

/* The same, where the caller holds the request mutably. */
uint64_t Request_GetStoreMut(REQUEST* Request)
    _requires(Request->Base._active && Request->Params._active)
    _requires(Request->Params.Index < Request->Params.Count)
    _ensures(Request->Params.Index < Request->Params.Count)
{
    return Base_GetStore(&Request->Base);
}
