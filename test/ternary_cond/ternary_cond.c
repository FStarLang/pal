#include "pal.h"
#include <stdbool.h>

/* Helper: identity function (impure in Pulse — not marked _pure) */
int identity(int x)
    _ensures(return == x)
{
    return x;
}

/* Pure spec function for condition tests */
_pure bool is_positive(int x)
    _ensures(return == (x > 0))
{
    return x > 0;
}

/* Impure wrapper: calls is_positive, usable in impure contexts */
bool check_positive(int x)
    _ensures(return == is_positive(x))
{
    return x > 0;
}

/* Pure ternary: all operands are pure expressions */
int pure_max(int x, int y)
    _ensures(x > y ==> return == x)
    _ensures(!(x > y) ==> return == y)
{
    return x > y ? x : y;
}

/* Impure then-branch only */
int impure_then(int x, int y)
    _ensures(x > y ==> return == x)
    _ensures(!(x > y) ==> return == y)
{
    return x > y ? identity(x) : y;
}

/* Impure else-branch only */
int impure_else(int x, int y)
    _ensures(x > y ==> return == x)
    _ensures(!(x > y) ==> return == y)
{
    return x > y ? x : identity(y);
}

/* Both branches impure */
int impure_both(int x, int y)
    _ensures(x > y ==> return == x)
    _ensures(!(x > y) ==> return == y)
{
    return x > y ? identity(x) : identity(y);
}

/* Impure condition only */
int impure_cond(int x, int a, int b)
    _ensures(is_positive(x) ==> return == a)
    _ensures(!is_positive(x) ==> return == b)
{
    return check_positive(x) ? a : b;
}

/* Impure condition + then-branch */
int impure_cond_then(int x, int a, int b)
    _ensures(is_positive(x) ==> return == a)
    _ensures(!is_positive(x) ==> return == b)
{
    return check_positive(x) ? identity(a) : b;
}

/* Impure condition + else-branch */
int impure_cond_else(int x, int a, int b)
    _ensures(is_positive(x) ==> return == a)
    _ensures(!is_positive(x) ==> return == b)
{
    return check_positive(x) ? a : identity(b);
}

/* All three operands impure */
int impure_all(int x, int a, int b)
    _ensures(is_positive(x) ==> return == a)
    _ensures(!is_positive(x) ==> return == b)
{
    return check_positive(x) ? identity(a) : identity(b);
}
