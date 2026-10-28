#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void write_optional(_nullable _out int32_t *p)
    _ensures(_inline_pulse(unless_null $(p) (int32_t_pts_to $(p) 1.0R 42l)))
{
    if (p != NULL) {
        *p = 42;
    }
}

void write_optional_default(_nullable _out int32_t *p)
{
    if (p != NULL) {
        *p = 17;
    }
}

void write_optional_early(_nullable _out int32_t *p)
    _ensures(_inline_pulse(unless_null $(p) (int32_t_pts_to $(p) 1.0R 42l)))
{
    if (p == NULL) {
        return;
    }
    *p = 42;
}

void write_optional_addressed(_nullable _out int32_t *p)
    _ensures(_inline_pulse(unless_null $(p) (int32_t_pts_to $(p) 1.0R 42l)))
{
    _assert(_live(p));
    if (p != NULL) {
        *p = 42;
    }
}

void rewrite_optional(_nullable _out int32_t *p)
    _ensures(_inline_pulse(unless_null $(p) (int32_t_pts_to $(p) 1.0R 43l)))
{
    if (p != NULL) {
        *p = 42;
    }
    if (p != NULL) {
        *p = 43;
    }
}

void forward_optional(_nullable _out int32_t *p)
    _ensures(_inline_pulse(unless_null $(p) (int32_t_pts_to $(p) 1.0R 42l)))
{
    write_optional(p);
}

void write_nonnull(_out int32_t *p)
    _ensures(*p == 42)
{
    *p = 42;
}

void call_nonnull_guarded(_nullable _out int32_t *p)
    _ensures(_inline_pulse(unless_null $(p) (int32_t_pts_to $(p) 1.0R 42l)))
{
    if (p != NULL) {
        write_nonnull(p);
    }
}

void call_optional_null(void)
{
    _ghost_stmt(intro_unless_null_null null (int32_t_pts_to_uninit null));
    write_optional(NULL);
    _ghost_stmt(elim_unless_null_null null _);
}

int32_t call_optional_nonnull(void)
    _ensures(return == 42)
{
    int32_t value;
    _ghost_stmt(int32_t_pts_to_uninit_not_null $&(value));
    _ghost_stmt(intro_unless_null $&(value) (int32_t_pts_to_uninit $&(value)));
    write_optional(&value);
    _ghost_stmt(elim_unless_null $&(value) _);
    return value;
}

struct pair {
    int32_t a;
    uint32_t b;
};

void write_optional_fields(_nullable _out struct pair *p)
    _ensures(_inline_pulse(unless_null $(p) (struct_pair_pts_to $(p) 1.0R ({ fld_a = 42l; fld_b = 7ul }))))
{
    if (p != NULL) {
        p->a = 42;
        p->b = 7;
    }
}

void write_optional_fields_addressed(_nullable _out struct pair *p)
    _ensures(_inline_pulse(unless_null $(p) (struct_pair_pts_to $(p) 1.0R ({ fld_a = 42l; fld_b = 7ul }))))
{
    _assert(_live(p));
    if (p != NULL) {
        p->a = 42;
        p->b = 7;
    }
}

int32_t call_optional_fields(void)
    _ensures(return == 42)
{
    struct pair value;
    _ghost_stmt(struct_pair_scatter_uninit $&(value));
    _ghost_stmt(int32_t_pts_to_uninit_not_null $&(value.a));
    _ghost_stmt(struct_pair_gather_uninit $&(value));
    _ghost_stmt(intro_unless_null $&(value) (struct_pair_pts_to_uninit $&(value)));
    write_optional_fields(&value);
    _ghost_stmt(elim_unless_null $&(value) _);
    return value.a;
}
