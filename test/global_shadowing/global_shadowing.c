#include "pal.h"

/* A parameter must shadow the global in both the body and the contract. */
const int count = 99;
int mutable_count;

int echo(int count)
    _ensures(return == count)
{
    return count;
}

int correct_caller(void)
    _ensures(return == 5)
{
    return echo(5);
}

int assign_parameter(int count)
    _requires(count > 0 && count < 10)
    _ensures(return == count + 1)
{
    count = count + 1;
    return count;
}

int local_value(void)
    _ensures(return == 7)
{
    int count = 7;
    return count;
}

/* Address-taking must select the local storage, not Global_count's address. */
int parameter_address(int count)
    _ensures(return == 8)
{
    int *p = &count;
    *p = 8;
    return count;
}

int local_address(void)
    _ensures(return == 9)
{
    int count = 7;
    int *p = &count;
    *p = 9;
    return count;
}

/* A shadowing parameter is readable even when the global is mutable. */
int shadow_mutable(int mutable_count)
    _ensures(return == mutable_count)
{
    return mutable_count;
}

int call_shadow_mutable(void)
    _ensures(return == 6)
{
    return shadow_mutable(6);
}

int read_global(void)
    _ensures(return == 99)
{
    return count;
}
