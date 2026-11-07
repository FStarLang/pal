// Tests: Increment, decrement, and compound assignment operators
//
// Compound assignments (+=, -=, *=, etc.) are tested in binary_ops.c.
// These operators are syntactic sugar for existing supported operations.
// pal desugars them during translation.

#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

uint32_t test_post_incr(uint32_t a)
    _requires(a < 1000)
    _ensures(return == a + 1)
{
    a++;
    return a;
}

uint32_t test_pre_incr(uint32_t a)
    _requires(a < 1000)
    _ensures(return == a + 1)
{
    ++a;
    return a;
}

uint32_t test_post_decr(uint32_t a)
    _requires(a > 0)
    _ensures(return == a - 1)
{
    a--;
    return a;
}

uint32_t test_pre_decr(uint32_t a)
    _requires(a > 0)
    _ensures(return == a - 1)
{
    --a;
    return a;
}

int test_incr_decr(int a)
    _requires(a < INT32_MAX - 1)
{
    a++;
    ++a;
    a--;
    --a;
    return a;
}

int test_compound_assign(int a)
    _requires(INT32_MIN <= (_specint) a * 2)
    _requires((_specint) a * 2 <= INT32_MAX)
{
    a += 1;
    a -= 1;
    a *= 2;
    a /= 1;
    return a;
}

size_t test_sizet_incr(size_t a)
    _requires((_specnat) a < UINT32_MAX)
{
    a++;
    a--;
    return a;
}

uint32_t test_u32_incr(uint32_t a)
    _requires(a < UINT32_MAX)
{
    a++;
    a--;
    return a;
}

uint8_t test_u8_pre_incr_wrap(void)
    _ensures(return == 0)
{
    uint8_t a = UINT8_MAX;
    ++a;
    return a;
}

uint16_t test_u16_post_incr_wrap(void)
    _ensures(return == 0)
{
    uint16_t a = UINT16_MAX;
    a++;
    return a;
}

uint32_t test_u32_pre_decr_wrap(void)
    _ensures(return == UINT32_MAX)
{
    uint32_t a = 0;
    --a;
    return a;
}

uint64_t test_u64_post_decr_wrap(void)
    _ensures(return == UINT64_MAX)
{
    uint64_t a = 0;
    a--;
    return a;
}

// Check expression results as well as the updated variables.

int8_t test_i8_post_incr_result(void)
    _ensures(return == 5)
{
    int8_t x = 5;
    int8_t result = x++;
    _assert(x == 6);
    return result;
}

int8_t test_i8_pre_incr_result(void)
    _ensures(return == 6)
{
    int8_t x = 5;
    int8_t result = ++x;
    _assert(x == 6);
    return result;
}

int8_t test_i8_post_decr_result(void)
    _ensures(return == 5)
{
    int8_t x = 5;
    int8_t result = x--;
    _assert(x == 4);
    return result;
}

int8_t test_i8_pre_decr_result(void)
    _ensures(return == 4)
{
    int8_t x = 5;
    int8_t result = --x;
    _assert(x == 4);
    return result;
}

int16_t test_i16_post_incr_result(void)
    _ensures(return == 5)
{
    int16_t x = 5;
    int16_t result = x++;
    _assert(x == 6);
    return result;
}

int16_t test_i16_pre_incr_result(void)
    _ensures(return == 6)
{
    int16_t x = 5;
    int16_t result = ++x;
    _assert(x == 6);
    return result;
}

int16_t test_i16_post_decr_result(void)
    _ensures(return == 5)
{
    int16_t x = 5;
    int16_t result = x--;
    _assert(x == 4);
    return result;
}

int16_t test_i16_pre_decr_result(void)
    _ensures(return == 4)
{
    int16_t x = 5;
    int16_t result = --x;
    _assert(x == 4);
    return result;
}

int32_t test_i32_post_incr_result(void)
    _ensures(return == 5)
{
    int32_t x = 5;
    int32_t result = x++;
    _assert(x == 6);
    return result;
}

int32_t test_i32_pre_incr_result(void)
    _ensures(return == 6)
{
    int32_t x = 5;
    int32_t result = ++x;
    _assert(x == 6);
    return result;
}

int32_t test_i32_post_decr_result(void)
    _ensures(return == 5)
{
    int32_t x = 5;
    int32_t result = x--;
    _assert(x == 4);
    return result;
}

int32_t test_i32_pre_decr_result(void)
    _ensures(return == 4)
{
    int32_t x = 5;
    int32_t result = --x;
    _assert(x == 4);
    return result;
}

int64_t test_i64_post_incr_result(void)
    _ensures(return == 5)
{
    int64_t x = 5;
    int64_t result = x++;
    _assert(x == 6);
    return result;
}

int64_t test_i64_pre_incr_result(void)
    _ensures(return == 6)
{
    int64_t x = 5;
    int64_t result = ++x;
    _assert(x == 6);
    return result;
}

int64_t test_i64_post_decr_result(void)
    _ensures(return == 5)
{
    int64_t x = 5;
    int64_t result = x--;
    _assert(x == 4);
    return result;
}

int64_t test_i64_pre_decr_result(void)
    _ensures(return == 4)
{
    int64_t x = 5;
    int64_t result = --x;
    _assert(x == 4);
    return result;
}

uint8_t test_u8_post_incr_result(void)
    _ensures(return == 5)
{
    uint8_t x = 5;
    uint8_t result = x++;
    _assert(x == 6);
    return result;
}

uint8_t test_u8_pre_incr_result(void)
    _ensures(return == 6)
{
    uint8_t x = 5;
    uint8_t result = ++x;
    _assert(x == 6);
    return result;
}

uint8_t test_u8_post_decr_result(void)
    _ensures(return == 5)
{
    uint8_t x = 5;
    uint8_t result = x--;
    _assert(x == 4);
    return result;
}

uint8_t test_u8_pre_decr_result(void)
    _ensures(return == 4)
{
    uint8_t x = 5;
    uint8_t result = --x;
    _assert(x == 4);
    return result;
}

uint16_t test_u16_post_incr_result(void)
    _ensures(return == 5)
{
    uint16_t x = 5;
    uint16_t result = x++;
    _assert(x == 6);
    return result;
}

uint16_t test_u16_pre_incr_result(void)
    _ensures(return == 6)
{
    uint16_t x = 5;
    uint16_t result = ++x;
    _assert(x == 6);
    return result;
}

uint16_t test_u16_post_decr_result(void)
    _ensures(return == 5)
{
    uint16_t x = 5;
    uint16_t result = x--;
    _assert(x == 4);
    return result;
}

uint16_t test_u16_pre_decr_result(void)
    _ensures(return == 4)
{
    uint16_t x = 5;
    uint16_t result = --x;
    _assert(x == 4);
    return result;
}

uint32_t test_u32_post_incr_result(void)
    _ensures(return == 5)
{
    uint32_t x = 5;
    uint32_t result = x++;
    _assert(x == 6);
    return result;
}

uint32_t test_u32_pre_incr_result(void)
    _ensures(return == 6)
{
    uint32_t x = 5;
    uint32_t result = ++x;
    _assert(x == 6);
    return result;
}

uint32_t test_u32_post_decr_result(void)
    _ensures(return == 5)
{
    uint32_t x = 5;
    uint32_t result = x--;
    _assert(x == 4);
    return result;
}

uint32_t test_u32_pre_decr_result(void)
    _ensures(return == 4)
{
    uint32_t x = 5;
    uint32_t result = --x;
    _assert(x == 4);
    return result;
}

uint64_t test_u64_post_incr_result(void)
    _ensures(return == 5)
{
    uint64_t x = 5;
    uint64_t result = x++;
    _assert(x == 6);
    return result;
}

uint64_t test_u64_pre_incr_result(void)
    _ensures(return == 6)
{
    uint64_t x = 5;
    uint64_t result = ++x;
    _assert(x == 6);
    return result;
}

uint64_t test_u64_post_decr_result(void)
    _ensures(return == 5)
{
    uint64_t x = 5;
    uint64_t result = x--;
    _assert(x == 4);
    return result;
}

uint64_t test_u64_pre_decr_result(void)
    _ensures(return == 4)
{
    uint64_t x = 5;
    uint64_t result = --x;
    _assert(x == 4);
    return result;
}

size_t test_sizet_post_incr_result(void)
    _ensures(return == 5)
{
    size_t x = 5;
    size_t result = x++;
    _assert(x == 6);
    return result;
}

size_t test_sizet_pre_incr_result(void)
    _ensures(return == 6)
{
    size_t x = 5;
    size_t result = ++x;
    _assert(x == 6);
    return result;
}

size_t test_sizet_post_decr_result(void)
    _ensures(return == 5)
{
    size_t x = 5;
    size_t result = x--;
    _assert(x == 4);
    return result;
}

size_t test_sizet_pre_decr_result(void)
    _ensures(return == 4)
{
    size_t x = 5;
    size_t result = --x;
    _assert(x == 4);
    return result;
}
