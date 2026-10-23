#include "pal.h"

typedef long long (*rank_function)(long long);

long function_rank_call(rank_function f, long value)
{
    return ((long (*)(long))f)(value);
}
