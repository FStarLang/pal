#include "pal.h"
#include <stdint.h>

int8_t cast_literal_to_int8(void)
    _ensures(return == -1)
{
    return (int8_t)255;
}

uint8_t cast_literal_to_uint8(void)
    _ensures(return == UINT8_MAX)
{
    return (uint8_t)511;
}

int16_t cast_literal_to_int16(void)
    _ensures(return == -1)
{
    return (int16_t)65535;
}

uint16_t cast_literal_to_uint16(void)
    _ensures(return == UINT16_MAX)
{
    return (uint16_t)131071;
}

#define GENERATED_CODE_FIRST ((int32_t)0x80010001L)
#define GENERATED_CODE_SECOND ((int32_t)0x80010002L)
#define GENERATED_CODE_LIST \
    X(GENERATED_CODE_FIRST) \
    X(GENERATED_CODE_SECOND)

uint8_t is_direct_code(int32_t code)
{
    switch (code)
    {
    case (int32_t)0x80010001L:
    case (int32_t)0x80010002L:
        return 1;
    default:
        return 0;
    }
}

uint8_t is_generated_code(int32_t code)
{
    switch (code)
    {
#define X(CODE) \
    case CODE:
        GENERATED_CODE_LIST
#undef X
        return 1;
    default:
        return 0;
    }
}

uint32_t cast_literal_to_uint32(void)
    _ensures(return == 1)
{
    return (uint32_t)4294967297ULL;
}

int64_t cast_literal_to_int64(void)
    _ensures(return == -1)
{
    return (int64_t)UINT64_MAX;
}

uint64_t uint64_max_literal(void)
    _ensures(return == UINT64_MAX)
{
    return UINT64_MAX;
}

uint64_t preserve_representable_uint64_cast(void)
    _ensures(return == INT64_MAX)
{
    return (uint64_t)INT64_MAX;
}
