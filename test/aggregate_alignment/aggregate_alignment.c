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

struct __attribute__((aligned(256))) overaligned_record {
    uint32_t value;
};

union __attribute__((aligned(64))) overaligned_union {
    uint32_t value;
    uint64_t other;
};

void initialize_overaligned(_out struct overaligned_record *p)
    _ensures(p->value == 42)
{
    *p = (struct overaligned_record){ .value = 42 };
}

uint32_t overaligned_local(void)
    _ensures(return == 42)
{
    struct overaligned_record p;
    initialize_overaligned(&p);
    return p.value;
}

uint32_t overaligned_union_local(void)
    _ensures(return == 42)
{
    union overaligned_union p = { .value = 42 };
    return p.value;
}

uint32_t overaligned_array(void)
    _ensures(return == 42)
{
    struct overaligned_record p[2] = {{ .value = 1 }, { .value = 42 }};
    return p[1].value;
}
