#include "pal.h"
#include <stdint.h>

typedef struct D { uint32_t State; } D;

uint32_t UseScalar(const uint32_t* p)
  _preserves_value(*p)
{
    return *p;
}

uint32_t ReproScalar(_array uint32_t* A, uint16_t Count, uint16_t Index)
  _requires(A._length == Count)
{
    if (Index < Count) {
        return UseScalar(&A[Index]);
    }
    return 0;
}

uint32_t UseStruct(const D* p)
{
    return p->State;
}

uint32_t ReproStruct(_array D* A, uint16_t Count, uint16_t Index)
  _requires(A._length == Count)
{
    if (Index < Count) {
        return UseStruct(&A[Index]);
    }
    return 0;
}
