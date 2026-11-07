#include "pal.h"
#include <stdint.h>

struct __attribute__((aligned(8))) aligned_record {
    uint8_t bytes[8];
};

void initialize(_out struct aligned_record *p)
{
    *p = (struct aligned_record){ .bytes = {42} };
}

void misaligned_storage(_plain struct aligned_record *p)
    _requires(_inline_pulse(
        array_pts_to_uninit uint8_t_repr 1 (SizeT.v uint8_t_alignof) 8
            ($(p) +! struct_aligned_record_offsetof_bytes)))
    _requires((_Bool)_inline_pulse(not (aligned $(p) 8sz)))
    _ensures(_inline_pulse(
        exists* (value: struct_aligned_record).
            struct_aligned_record_pts_to $(p) 1.0R value))
{
    _ghost_stmt(fold (struct_aligned_record_padding $(p) 1.0R));
    _ghost_stmt(struct_aligned_record_gather_uninit $(p));
    initialize(p);
}
