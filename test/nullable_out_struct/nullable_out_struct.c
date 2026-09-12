#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef struct pair
{
    uint64_t fst;
    uint64_t snd;
} pair;

// Two optional outputs, each filled from a member of a shared structure. The
// structure's ownership is what the two branches disagree about at the join.
void opt_two_from_struct(
    const pair* Src,
    _nullable _out _refine(*this == Src->fst) uint64_t* A,
    _nullable _out _refine(*this == Src->snd) uint64_t* B)
{
    if (A != NULL)
    {
        *A = Src->fst;
    }

    if (B != NULL)
    {
        *B = Src->snd;
    }
}
