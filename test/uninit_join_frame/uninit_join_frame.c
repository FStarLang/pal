#include "pal.h"
#include <stddef.h>
#include <stdint.h>

int delayed_scalar(int *p, _Bool write)
    _ensures(return == *p)
{
    int result;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 1;
    }
    result = *p;
    return result;
}

union result {
    int value;
    unsigned bits;
};

int delayed_union(int *p, _Bool write)
    _ensures(return == *p)
{
    union result result;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 2;
    }
    result.value = *p;
    return result.value;
}

int conditional_scalar(int *p, _Bool write)
    _ensures(return == (write ? 7 : _old(*p)))
{
    int result;
    _ghost_stmt(with initial. assert int32_t_pts_to $(p) 1.0R initial);
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v **
                pure (v == (if $(write) then 7l else initial))))
    {
        result = 7;
        *p = result;
    }
    result = *p;
    return result;
}

int conditional_else(_Bool choose)
    _ensures(return == (choose ? 1 : 2))
{
    int temporary;
    int result;
    if (choose) {
        result = 1;
    } else {
        temporary = 2;
        result = temporary;
    }
    return result;
}

int conditional_union(int *p, _Bool first, _Bool second)
    _ensures(return == (first && second ? 3 : _old(*p)))
{
    union result result;
    if (first) {
        if (second) {
            result.value = 3;
            *p = result.value;
        }
    }
    result.value = *p;
    return result.value;
}

void delayed_output(_out int *out, int *p, _Bool write)
    _ensures(*out == *p)
{
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 1;
    }
    *out = *p;
}

void delayed_optional_output(_nullable _out int *out, int *p, _Bool write)
    _ensures(_inline_pulse(unless_null $(out) (int32_t_pts_to $(out) 1.0R $(*p))))
{
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 2;
    }
    if (out != NULL) {
        if (write)
            _ensures((_slprop)_inline_pulse(
                exists* v. int32_t_pts_to $&(*p) 1.0R v))
        {
            *p = 3;
        }
        *out = *p;
    }
}
