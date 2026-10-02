#include "pal.h"
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct Flags { bool A; bool B; } Flags;
typedef struct D { uint32_t State; uint64_t Ver; uint32_t Fl; Flags Flags; } D;
typedef struct BitFlags { uint32_t A : 1; uint32_t B : 3; } BitFlags;
typedef struct WithBits { BitFlags Flags; } WithBits;

void GetTwo(uint64_t* v, uint32_t* f)
  _ensures(true)
{
    *v = 1;
    *f = 2;
}

void SetD(D* d, uint32_t s)
  _ensures(true)
{
    d->State = s;
}

void InitD(_out D* d)
  _ensures(true)
{
    *d = (D){ .State = 0, .Ver = 0, .Fl = 0, .Flags = { .A = false, .B = false } };
}

void Writer(_array D* A, uint16_t Count, uint16_t Index)
  _requires(A._length == Count)
  _preserves_value(A._length)
{
    if (Index < Count) {
        A[Index].State = 3;
        SetD(&A[Index], 7);
        InitD(&A[Index]);
        GetTwo(&A[Index].Ver, &A[Index].Fl);
        A[Index].Flags.A = false;
        A[Index].Flags.B = true;
    }
}

void WriterLoop(_array D* A, size_t Count)
  _requires(A._length == Count)
  _preserves_value(A._length)
{
    size_t i = 0;
    while (i < Count)
      _invariant(_live(i))
      _invariant(_live(*A))
      _invariant(A._length == Count)
      _invariant(i <= Count)
    {
        SetD(&A[i], 11);
        GetTwo(&A[i].Ver, &A[i].Fl);
        A[i].Flags.A = true;
        A[i].Flags.B = false;
        i = i + 1;
    }
}

void WriteBitField(_array WithBits* A, size_t Count, size_t Index)
  _requires(A._length == Count)
  _preserves_value(A._length)
{
    if (Index < Count) {
        A[Index].Flags.A = 1;
        A[Index].Flags.B = 7;
    }
}
