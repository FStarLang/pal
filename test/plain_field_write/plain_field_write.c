#include "pal.h"
#include <stdint.h>

/* A `_plain` parameter whose contract gives only the bytes of one field
   holds no ownership of the struct, so a write to that field has no
   ownership to carry over to the struct's new value: the write lands in the
   field the contract gives, and nothing else is asked of it. */

struct ctx {
    uint32_t count;
};

struct obj {
    struct ctx *c;
    uint32_t state;
    uint32_t kind;
};

void set_state(_plain struct obj *o, uint32_t s)
    _requires(_inline_pulse(exists* v.
        uint32_t_pts_to ($(o) +! Struct_obj.struct_obj_offsetof_state) 1.0R v))
    _ensures(_inline_pulse(
        uint32_t_pts_to ($(o) +! Struct_obj.struct_obj_offsetof_state) 1.0R $(s)))
{
    o->state = s;
}

void set_both(_plain struct obj *o, uint32_t s)
    _requires(_inline_pulse(exists* v.
        uint32_t_pts_to ($(o) +! Struct_obj.struct_obj_offsetof_state) 1.0R v))
    _requires(_inline_pulse(exists* v.
        uint32_t_pts_to ($(o) +! Struct_obj.struct_obj_offsetof_kind) 1.0R v))
    _ensures(_inline_pulse(
        uint32_t_pts_to ($(o) +! Struct_obj.struct_obj_offsetof_state) 1.0R $(s)))
    _ensures(_inline_pulse(
        uint32_t_pts_to ($(o) +! Struct_obj.struct_obj_offsetof_kind) 1.0R $(s)))
{
    set_state(o, s);
    o->kind = s;
}
