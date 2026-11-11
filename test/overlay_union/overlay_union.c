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

/* A layer that sees only its own view. */
void Generic_SetStatus(GENERIC_REQUEST* Request, int32_t Status)
    _ensures(Request->Common.Status == Status)
    _ensures(Request->Common.State == _old(Request->Common.State))
{
    Request->Common.Status = Status;
}

uint32_t Base_GetActivityId(const BASE_REQUEST* Request)
    _requires(Request->BaseParams._active)
    _ensures(return == Request->BaseParams.Common.ActivityId)
{
    return Request->BaseParams.Common.ActivityId;
}

/* Three members of one union in one function: the library's view is lent to
   the library, the type's own parameters are written directly, and the
   scheduler's view is lent to the scheduler. Each write leaves the others'
   fields, which do not overlap it, as they were. */
void Mount_Step(MOUNT_REQUEST* Request)
    _requires(Request->Base.BaseParams._active && Request->Generic._active)
    _ensures(Request->Generic._active && Request->Generic.Common.Status == 0)
    _ensures(Request->Generic.Common.State == _old(Request->Generic.Common.State))
{
    uint32_t activityId = Base_GetActivityId(&Request->Base);
    Request->Params.Sequence = activityId + 1u;
    Generic_SetStatus(&Request->Generic, 0);
}

/* Initialising every view's fields through their own members, from storage
   nothing was known about: a write needs no member to be readable. */
void Mount_Init(MOUNT_REQUEST* Request, uint32_t ActivityId)
    _ensures(Request->Params.Context == 7u && Request->Params.Sequence == 0u)
    _ensures(Request->Base.BaseParams.Common.Store == 3u)
    _ensures(Request->Base.BaseParams.Common.ActivityId == ActivityId)
    _ensures(Request->Generic.Common.State == 1u)
    _ensures(Request->Generic.Common.Status == 0)
{
    Request->Generic.Common.State = 1u;
    Request->Generic.Common.Status = 0;
    Request->Base.BaseParams.Common.Store = 3u;
    Request->Base.BaseParams.Common.ActivityId = ActivityId;
    Request->Params.Context = 7u;
    Request->Params.Sequence = 0u;
}

/* The type's own field changes; the library's and the scheduler's do not. */
void Mount_SetSequence(MOUNT_REQUEST* Request, uint32_t Sequence)
    _requires(Request->Base.BaseParams._active && Request->Generic._active)
    _ensures(Request->Params.Sequence == Sequence)
    _ensures(Request->Base.BaseParams._active && Request->Generic._active)
    _ensures(Request->Base.BaseParams.Common.Store == _old(Request->Base.BaseParams.Common.Store))
    _ensures(Request->Base.BaseParams.Common.ActivityId ==
             _old(Request->Base.BaseParams.Common.ActivityId))
    _ensures(Request->Generic.Common.State == _old(Request->Generic.Common.State))
    _ensures(Request->Generic.Common.Status == _old(Request->Generic.Common.Status))
{
    Request->Params.Sequence = Sequence;
}

/* A constant subscript is a constant offset too. */
uint8_t Generic_Byte(const MOUNT_REQUEST* Request)
    _requires(Request->Generic._active)
    _ensures(return == Request->Generic.Parameters[20])
{
    return Request->Base.Generic.Parameters[20];
}

/* A scheduler call that promises the parameter bytes back unchanged. */
void Generic_Complete(GENERIC_REQUEST* Request)
    _ensures(Request->Common.Status == 0)
    _ensures(_forall(size_t k, k < 32 ==> Request->Parameters[k] == _old(Request->Parameters[k])))
{
    Request->Common.Status = 0;
}

/* Lending the scheduler's whole view keeps the library's fields, which live
   in its parameter bytes: the bytes are what the array view says they are. */
void Mount_Complete(MOUNT_REQUEST* Request)
    _requires(Request->Base.BaseParams._active && Request->Generic._active)
    _ensures(Request->Base.BaseParams._active)
    _ensures(Request->Base.BaseParams.Common.ActivityId ==
             _old(Request->Base.BaseParams.Common.ActivityId))
    _ensures(Request->Base.BaseParams.Common.Store == _old(Request->Base.BaseParams.Common.Store))
{
    Generic_Complete(&Request->Generic);
}
