#include "vocab.h"

_pure
int sign(int x)
{
    return x >= 0 ? 1 : -1;
}

int clamp(int x)
{
    return x >= 0 ? x : 0;
}
