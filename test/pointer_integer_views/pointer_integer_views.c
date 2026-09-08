#include "pal.h"
#include <stdint.h>

/* Deliberately test narrower mathematical integer views. The host compiler's
 * pointer-size warnings are expected here, not PAL translation failures. */
#pragma GCC diagnostic ignored "-Wint-to-pointer-cast"
#pragma GCC diagnostic ignored "-Wpointer-to-int-cast"

/* Each signed/unsigned width roundtrips values in its own representable
 * range. No claim is made that arbitrary pointers survive an integer cast. */
#define ROUNDTRIP(name, type)                 \
    _pure void *from_##name(type x)           \
    {                                        \
        return (void *)x;                     \
    }                                        \
    _pure type to_##name(void *p)             \
    {                                        \
        return (type)p;                       \
    }                                        \
    void roundtrip_##name(type x)             \
    {                                        \
        void *p = from_##name(x);             \
        type y = to_##name(p);                \
        _assert(y == x);                      \
    }

ROUNDTRIP(i8, int8_t)
ROUNDTRIP(u8, uint8_t)
ROUNDTRIP(i16, int16_t)
ROUNDTRIP(u16, uint16_t)
ROUNDTRIP(i32, int32_t)
ROUNDTRIP(u32, uint32_t)
ROUNDTRIP(i64, int64_t)
ROUNDTRIP(u64, uint64_t)

void variable_zero(int64_t zero)
    _requires(zero == 0)
{
    void *p = (void *)zero;
    _assert(p == (void *)0);
    int64_t s = (int64_t)p;
    uint64_t u = (uint64_t)p;
    _assert(s == 0);
    _assert(u == 0);
}

/* PointerToIntegral must run even when recursive null detection finds a
 * null inside the expression. IntegralToPointer still preserves literal
 * null handling, including the nested roundtrip. */
void literal_null(void)
{
    int64_t s = (int64_t)(void *)0;
    uint8_t u = (uint8_t)(void *)0;
    void *p = (void *)(int64_t)(void *)0;
    _assert(s == 0);
    _assert(u == 0);
    _assert(p == (void *)0);
}

void negative_views(int8_t x)
    _requires(x < 0)
{
    void *p = (void *)x;
    int64_t wide = (int64_t)p;
    uint8_t small = (uint8_t)p;
    uint64_t large = (uint64_t)p;
    _assert(wide == (int64_t)x);
    _assert(small == (uint8_t)x);
    _assert(large == (uint64_t)(int64_t)x);
}

void narrowing(void)
{
    void *p = from_i64(257);
    uint8_t u = (uint8_t)p;
    int8_t s = (int8_t)p;
    _assert(u == 1);
    _assert(s == 1);

    void *high_bit = from_u16(128);
    int8_t negative = (int8_t)high_bit;
    _assert(negative == -128);

    void *maximum = from_u64(UINT64_MAX);
    int64_t signed_maximum = (int64_t)maximum;
    uint16_t low_bits = (uint16_t)maximum;
    _assert(signed_maximum == -1);
    _assert(low_bits == UINT16_MAX);
}

/* A typed _core_ref is also a raw value; casts must not add ownership. */
void core_view(_core_ref int *p)
{
    int64_t direct = (int64_t)p;
    int64_t through_void = (int64_t)(void *)p;
    _assert(direct == through_void);
}

/* Exercise pure value comparison and early return separately from casts. */
_pure int classify_raw(void *p)
{
    if (p == (void *)0)
        return 10;
    return 20;
}

void classify_null(void)
{
    int value = classify_raw((void *)0);
    _assert(value == 10);
}
