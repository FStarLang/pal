#include "pal.h"

int foo(void) _ensures(return == 1);
int foo(void) _ensures(return == 1) { return 1; }
int Foo(void) _ensures(return == 2) { return 2; }
int foo_1(void) _ensures(return == 3) { return 3; }

int use_lower(void) _ensures(return == 1) { return foo(); }
int use_upper(void) _ensures(return == 2) { return Foo(); }
int use_suffix(void) _ensures(return == 3) { return foo_1(); }

int use_lower_pointer(void) _ensures(return == 1)
{
    int (*fp)(void) = foo;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_foo_2.func_foo__fp);
    return fp();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

int use_upper_pointer(void) _ensures(return == 2)
{
    int (*fp)(void) = &Foo;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_Foo.func_foo__fp_1);
    return fp();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

int use_suffix_pointer(void) _ensures(return == 3)
{
    int (*fp)(void) = foo_1;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_foo_1.func_foo_1__fp);
    return fp();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
