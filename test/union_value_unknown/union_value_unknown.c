#include "pal.h"

union value {
    int number;
    _Bool flag;
};

union value copy_unknown(const union value *p)
{
    return *p;
}
