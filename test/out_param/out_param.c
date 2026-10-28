#include "pal.h"
#include <stdbool.h>

void init_value(_out int *x)
    _ensures(*x == 42)
{
    *x = 42;
}

int call_init_value()
    _ensures(return == 42)
{
    int x;
    init_value(&x);
    return x;
}

void init_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b) {
        _assert(_live(x));
        *x = 42;
    } else {
        _assert(_live(x));
        *x = 42;
    }
}

void init_by_call_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b) {
        _assert(_live(x));
    }
    init_value(x);
}

void init_mixed_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b)
        _ensures(_inline_pulse(
            exists* (v: Int32.t).
                int32_t_pts_to $(x) 1.0R v **
                pure (Int32.v v == 42) **
                ptr_pts_to $&(x) 1.0R $(x)))
    {
        *x = 42;
    } else {
        init_value(x);
    }
}

void init_from_owned_storage(_plain int *x)
    _requires(_inline_pulse(int32_t_pts_to_uninit $(x)))
    _ensures(_inline_pulse(int32_t_pts_to $(x) 1.0R 42l))
{
    _assert(_live(x));
    init_value(x);
}

void init_from_local_owned_storage(_plain int *x)
    _requires(_inline_pulse(int32_t_pts_to_uninit $(x)))
    _ensures(_inline_pulse(int32_t_pts_to $(x) 1.0R 42l))
{
    int *destination = x;
    init_value(destination);
}

void init_again(_out int *x)
    _ensures(*x == 42)
{
    *x = 0;
    init_value(x);
}

void init_rebound_after_write(_out int *x, int *other)
    _ensures(*x == 7 && *other == 42)
{
    *x = 7;
    x = other;
    init_value(x);
}

void init_other_owned_storage(_plain int *x, _plain int *other)
    _requires(_inline_pulse(
        int32_t_pts_to_uninit $(x) ** int32_t_pts_to_uninit $(other)))
    _ensures(_inline_pulse(
        int32_t_pts_to_uninit $(x) ** int32_t_pts_to $(other) 1.0R 42l))
{
    x = other;
    init_value(x);
}

struct output_record {
    int a;
    int b;
};

void init_record(_out struct output_record *x)
    _ensures(x->a == 42 && x->b == 7)
{
    *x = (struct output_record){ .a = 42, .b = 7 };
}

void init_record_from_owned_storage(_plain struct output_record *x)
    _requires(_inline_pulse(struct_output_record_pts_to_uninit $(x)))
    _ensures(_inline_pulse(
        struct_output_record_pts_to $(x) 1.0R ({ fld_a = 42l; fld_b = 7l })))
{
    init_record(x);
}

void init_record_from_local_owned_storage(_plain struct output_record *x)
    _requires(_inline_pulse(struct_output_record_pts_to_uninit $(x)))
    _ensures(_inline_pulse(
        struct_output_record_pts_to $(x) 1.0R ({ fld_a = 42l; fld_b = 7l })))
{
    struct output_record *destination = x;
    init_record(destination);
}

void init_record_again(_out struct output_record *x)
    _ensures(x->a == 42 && x->b == 7)
{
    *x = (struct output_record){ .a = 0, .b = 0 };
    init_record(x);
}