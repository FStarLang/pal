#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Layered request views whose fields are not only fixed-width integers:
   pointers, function pointers, `bool` and `size_t`. */
typedef void (*COMPLETION)(void* Context);

typedef struct _LOWER_COMMON
{
    void* Owner;
    COMPLETION Completion;
    size_t Length;
    bool Pending;
} LOWER_COMMON;
typedef struct _LOWER_STATUS { int32_t Code; uint32_t Location; } LOWER_STATUS;
typedef union _LOWER_STATUS_PLUS { LOWER_STATUS Status; uint64_t Opaque; } LOWER_STATUS_PLUS;

/* A union the program also uses as a value, so it keeps its tagged model;
   inside the overlay it is an island, bytes the view does not look into. */
typedef union _CODE_PLUS { LOWER_STATUS Status; uint64_t Opaque; } CODE_PLUS;

CODE_PLUS Code_Zero(void)
    _ensures(return.Opaque._active && return.Opaque == 0)
{
    CODE_PLUS c;
    c.Opaque = 0;
    return c;
}

/* A one-byte struct of bit-fields, kept in an array. */
typedef struct _SLOT { uint8_t Level : 3; uint8_t Mark : 5; } SLOT;

/* The lower layer's request. Its parameter area is an anonymous union of
   byte arrays: everything an `_overlay` union reaches is part of the same
   bytes, so this union is an overlay union too, and the lower view of the
   area is its bytes, whatever the upper layer stored there -- pointers
   included. */
typedef struct _LOWER_REQUEST
{
    union
    {
        char ParamsOpaque[32];
        char Parameters[32];
    };
    LOWER_COMMON Common;
    LOWER_STATUS_PLUS Result;
    CODE_PLUS Saved;
    SLOT Stack[4];
} LOWER_REQUEST;

typedef struct _UPPER_PARAMS
{
    uint32_t* Cursor;
    bool Retry;
    uint32_t Count;
} UPPER_PARAMS;
typedef union _overlay _UPPER_REQUEST
{
    UPPER_PARAMS Params;
    LOWER_REQUEST Lower;
} UPPER_REQUEST;

/* Every kind of leaf written through its own member, from storage nothing
   was known about. */
void Upper_Init(UPPER_REQUEST* Request, void* Owner, COMPLETION Completion, uint32_t* Cursor)
    _ensures(Request->Lower.Common.Owner == Owner)
    _ensures(Request->Lower.Common.Completion == Completion)
    _ensures(Request->Lower.Common.Length == 0)
    _ensures(Request->Lower.Common.Pending == true)
    _ensures(Request->Params.Cursor == Cursor)
    _ensures(Request->Params.Retry == false)
    _ensures(Request->Params.Count == 3u)
{
    Request->Lower.Common.Owner = Owner;
    Request->Lower.Common.Completion = Completion;
    Request->Lower.Common.Length = 0;
    Request->Lower.Common.Pending = true;
    Request->Params.Cursor = Cursor;
    Request->Params.Retry = false;
    Request->Params.Count = 3u;
}

/* Reading each kind of leaf back. */
void* Upper_GetOwner(const UPPER_REQUEST* Request)
    _requires(Request->Lower._active)
    _ensures(return == Request->Lower.Common.Owner)
{
    return Request->Lower.Common.Owner;
}

size_t Upper_GetLength(const UPPER_REQUEST* Request)
    _requires(Request->Lower._active)
    _ensures(return == Request->Lower.Common.Length)
{
    return Request->Lower.Common.Length;
}

bool Upper_GetRetry(const UPPER_REQUEST* Request)
    _requires(Request->Params._active)
    _ensures(return == Request->Params.Retry)
{
    return Request->Params.Retry;
}

/* A lower layer that sees only its own view. */
void Lower_Finish(LOWER_REQUEST* Request, size_t Length)
    _ensures(Request->Common.Length == Length && Request->Common.Pending == false)
    _ensures(Request->Result.Opaque == _old(Request->Result.Opaque))
    _ensures(Request->Common.Owner == _old(Request->Common.Owner))
    _ensures(Request->Common.Completion == _old(Request->Common.Completion))
    _ensures(_unchanged(Request->Parameters))
{
    Request->Common.Length = Length;
    Request->Common.Pending = false;
}

/* Lending the lower view and writing the upper parameters: the pointers in
   each view that the other does not overlap keep their values. */
void Upper_Step(UPPER_REQUEST* Request)
    _requires(Request->Lower._active && Request->Params._active)
    _ensures(Request->Lower._active && Request->Params._active)
    _ensures(Request->Lower.Common.Owner == _old(Request->Lower.Common.Owner))
    _ensures(Request->Lower.Common.Pending == false)
    _ensures(Request->Params.Cursor == _old(Request->Params.Cursor))
    _ensures(Request->Params.Count == _old(Request->Params.Count) + 1u)
    _ensures(Request->Params.Retry == true)
    _requires(Request->Params.Count < 100u && Request->Lower.Common.Length < 4096)
{
    size_t n = Request->Lower.Common.Length;
    Lower_Finish(&Request->Lower, n + 1);
    Request->Params.Retry = true;
    Request->Params.Count = Request->Params.Count + 1u;
}

/* A member of a nested union that is a scalar, and a store through the
   other member that leaves the parameter area alone. */
void Lower_SetStatus(LOWER_REQUEST* Request, int32_t Code)
    _ensures(Request->Result.Status.Code == Code)
    _ensures(Request->Common.Owner == _old(Request->Common.Owner))
    _ensures(_unchanged(Request->Parameters))
{
    Request->Result.Status.Code = Code;
}

uint64_t Lower_GetOpaque(LOWER_REQUEST* Request)
    _requires(Request->Result.Opaque._active)
    _ensures(return == Request->Result.Opaque)
{
    return Request->Result.Opaque;
}

/* A store to the lower view keeps the island and the array of slots. */
void Lower_Reset(LOWER_REQUEST* Request)
    _ensures(Request->Common.Length == 0)
    _ensures(_unchanged(Request->Saved))
    _ensures(_unchanged(Request->Stack))
    _ensures(_unchanged(Request->Parameters))
{
    Request->Common.Length = 0;
}

/* An island loaded and stored whole, the way a status is saved and replaced:
   the store changes the island's bytes and no others. */
CODE_PLUS Lower_SwapSaved(LOWER_REQUEST* Request, CODE_PLUS Code)
    _requires(Request->Saved.Status._active)
    _ensures(Request->Common.Length == _old(Request->Common.Length))
    _ensures(_unchanged(Request->Parameters))
    _ensures(_unchanged(Request->Result))
    _ensures(_unchanged(Request->Stack))
{
    CODE_PLUS prev = Request->Saved;
    Request->Saved = Code;
    return prev;
}

/* The same through the outer overlay: the other view's fields survive. */
CODE_PLUS Upper_SwapSaved(UPPER_REQUEST* Request, CODE_PLUS Code)
    _requires(Request->Lower.Saved.Status._active)
    _requires(Request->Params._active && Request->Lower._active)
    _ensures(Request->Params._active)
    _ensures(Request->Params.Cursor == _old(Request->Params.Cursor))
    _ensures(Request->Params.Count == _old(Request->Params.Count))
    _ensures(_unchanged(Request->Lower.Common))
{
    CODE_PLUS prev = Request->Lower.Saved;
    Request->Lower.Saved = Code;
    return prev;
}

/* A union only ever declared, reached through a pointer: it is opaque. */
typedef union _LATER_REQUEST LATER_REQUEST;
typedef union _overlay _OUTER_REQUEST
{
    UPPER_PARAMS Params;
    LOWER_REQUEST Lower;
    LATER_REQUEST* Later;
} OUTER_REQUEST;

/* A store of an island, after reading the old value twice under
   short-circuit `||`: the island stays readable after the store. */
bool Outer_SetSaved(OUTER_REQUEST* Request, CODE_PLUS Code, bool Force)
    _requires(Request->Lower.Saved.Status._active)
    _requires(Code.Status._active)
    _ensures(Request->Lower.Saved.Status._active)
    _ensures(_unchanged(Request->Lower.Common))
{
    CODE_PLUS prev = Request->Lower.Saved;
    bool wasSet = Force || prev.Status.Code == 0 || prev.Status.Location == 0;
    Request->Lower.Saved = Code;
    return wasSet;
}
