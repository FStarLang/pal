#include "pal.h"
#include <stdlib.h>

struct point {
    int x;
    int y;
};

void set_x(struct point arr[])
    _requires(arr._length == 2)
{
    arr[0].x = 42;
}
