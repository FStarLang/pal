#include "pal.h"

/* foo and Foo (and foo_1 and Foo_1) would give modules F* considers the same,
   since it resolves module names case-insensitively. */

int foo(void) _ensures(return == 1);
int foo(void) _ensures(return == 1) { return 1; }
int Foo(void) _ensures(return == 2) { return 2; }
int foo_1(void) _ensures(return == 3) { return 3; }
int Foo_1(void) _ensures(return == 4) { return 4; }

int use_lower(void) _ensures(return == 1) { return foo(); }
int use_upper(void) _ensures(return == 2) { return Foo(); }
int use_suffix(void) _ensures(return == 3) { return foo_1(); }
int use_upper_suffix(void) _ensures(return == 4) { return Foo_1(); }

int use_lower_pointer(void) _ensures(return == 1)
{
    int (*fp)(void) = foo;
    return fp();
}

int use_upper_pointer(void) _ensures(return == 2)
{
    int (*fp)(void) = &Foo;
    return fp();
}

int use_suffix_pointer(void) _ensures(return == 3)
{
    int (*fp)(void) = foo_1;
    return fp();
}
