#include "pal.h"
#include <stdint.h>

struct __attribute__((aligned(8))) aligned_record {
    uint8_t bytes[8];
};

void initialize(_out struct aligned_record *p)
    _ensures(p->bytes[0] == 42)
{
    *p = (struct aligned_record){ .bytes = {42} };
}

void byte_roundtrip(_out struct aligned_record *p)
    _ensures(p->bytes[0] == 42)
{
    _ghost_stmt(
        struct_aligned_record_reveal_uninit $(p);
        struct_aligned_record_claim_uninit $(p));
    initialize(p);
    _ghost_stmt(
        with value. assert struct_aligned_record_pts_to $(p) 1.0R value;
        struct_aligned_record_reveal $(p);
        struct_aligned_record_conceal $(p) #_ #_ #value);
}
