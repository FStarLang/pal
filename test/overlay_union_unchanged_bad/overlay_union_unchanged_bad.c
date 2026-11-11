#include "pal.h"
#include <stdint.h>

/* Must fail: a store into the parameter area, which the contract promises
   is left as it was. */
typedef struct _LOWER_REQUEST
{
    union
    {
        char ParamsOpaque[16];
        char Parameters[16];
    };
    uint64_t Length;
} LOWER_REQUEST;

typedef union _overlay _UPPER_REQUEST
{
    uint64_t Header[2];
    LOWER_REQUEST Lower;
} UPPER_REQUEST;

void Lower_Scribble(LOWER_REQUEST* Request)
    _ensures(_unchanged(Request->Parameters))
{
    Request->Length = 0;
    Request->Parameters[3] = 1;
}
