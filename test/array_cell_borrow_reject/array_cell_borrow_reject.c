#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef struct Pair { uint32_t X; uint32_t Y; } Pair;

void UseOne(uint32_t* x) { *x = 1; }
void UseTwo(uint32_t* x, uint32_t* y) { *x = 1; *y = 2; }
void UseArray(uint32_t* x, _array Pair* a) { *x = 0; }
void UseIndex(uint32_t* x, size_t i) { *x = (uint32_t)i; }
void OutOne(_out uint32_t* x) { *x = 3; }
uint32_t ReadOne(uint32_t* x) { return *x; }

void DifferentIndex(_array Pair* A, size_t Count, size_t I, size_t J)
  _requires(A._length == Count)
{
    if (I < Count && J < Count) {
        UseTwo(&A[I].X, &A[J].Y);
    }
}

void DuplicateField(_array Pair* A, size_t Count, size_t I)
  _requires(A._length == Count)
{
    if (I < Count) {
        UseTwo(&A[I].X, &A[I].X);
    }
}

void ArrayAlsoPassed(_array Pair* A, size_t Count, size_t I)
  _requires(A._length == Count)
{
    if (I < Count) {
        UseArray(&A[I].X, A);
    }
}

void IndexAlsoPassed(_array Pair* A, size_t Count, size_t I)
  _requires(A._length == Count)
{
    if (I < Count) {
        UseIndex(&A[I].X, I);
    }
}

void SideEffectIndex(_array Pair* A, size_t Count, size_t I)
  _requires(A._length == Count)
{
    if (I + 1 < Count) {
        UseOne(&A[I++].X);
    }
}

void OutField(_array Pair* A, size_t Count, size_t I)
  _requires(A._length == Count)
{
    if (I < Count) {
        OutOne(&A[I].X);
    }
}

void AssignTargetOverlap(_array Pair* A, size_t Count, size_t I)
  _requires(A._length == Count)
{
    if (I < Count) {
        A[I].X = ReadOne(&A[I].Y);
    }
}
