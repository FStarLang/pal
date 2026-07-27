#include "pal.h"
#include <stdint.h>

/* Simple switch with break in every case */
int32_t day_type(int32_t day)
    _requires(day >= 0 && day <= 6)
    _ensures(day >= 1 && day <= 5 ==> return == 1)
    _ensures(day == 0 || day == 6 ==> return == 0)
{
    int32_t result = 0;
    switch (day) {
    case 1:
    case 2:
    case 3:
    case 4:
    case 5:
        result = 1;
        break;
    default:
        result = 0;
        break;
    }
    return result;
}

/* Grouped case labels share one terminal-break branch. */
int32_t classify(int32_t x)
    _requires(x >= 0 && x <= 3)
    _ensures(x == 0 ==> return == 10)
    _ensures((x == 1 || x == 2) ==> return == 20)
    _ensures(x == 3 ==> return == 30)
{
    int32_t r = 0;
    switch (x) {
    case 0:
        r = 10;
        break;
    case 1:
    case 2:
        r = 20;
        break;
    default:
        r = 30;
        break;
    }
    return r;
}

/* A genuine fall-through switch retains the general switch encoding. */
int32_t accumulate_with_fallthrough(int32_t x)
    _requires(x == 0 || x == 1)
    _ensures(x == 0 ==> return == 11)
    _ensures(x == 1 ==> return == 1)
{
    int32_t result = 0;
    switch (x) {
    case 0:
        result = 10;
    case 1:
        result = result + 1;
        break;
    }
    return result;
}

static void write_result(int32_t* _out result)
{
    *result = 42;
}

/* A switch join contract preserves resources across an output-writing call. */
int32_t call_in_case(int32_t x)
{
    int32_t result = 0;

    switch (x)
        _ensures(_live(x) && _live(result))
    {
    case 0:
        result = 1;
        break;
    default:
        write_result(&result);
        break;
    }

    return result;
}

/* Every path terminates in the switch; no trailing return is required. */
int32_t classify_with_returns(int32_t x)
{
    switch (x) {
    case 0:
        return 10;
    default:
        return 20;
    }
}

/* Sparse terminal-break cases retain source-order C switch semantics. */
int32_t sparse_unsorted(int32_t x)
    _ensures(x == -10 ==> return == 1)
    _ensures(x == 7 ==> return == 2)
    _ensures(x == 100 ==> return == 3)
    _ensures((x != -10 && x != 7 && x != 100) ==> return == 0)
{
    int32_t result = 0;
    switch (x) {
    case 100:
        result = 3;
        break;
    case -10:
        result = 1;
        break;
    case 7:
        result = 2;
        break;
    }
    return result;
}

_plain const char *sparse_string_name(
    int32_t x,
    _plain const char *fallback)
{
    const char *name = fallback;
    switch (x) {
    case 100:
        name = "hundred";
        break;
    case -10:
        name = "negative ten";
        break;
    case 7:
        name = "seven";
        break;
    }
    return name;
}

#ifndef SWITCH_SCALE_BRANCHES
#define SWITCH_SCALE_BRANCHES 16
#endif

#define SCALE_CASE() \
    case __COUNTER__: \
        result = 1; \
        break;
#define REPEAT_2(M) M() M()
#define REPEAT_4(M) REPEAT_2(M) REPEAT_2(M)
#define REPEAT_8(M) REPEAT_4(M) REPEAT_4(M)
#define REPEAT_16(M) REPEAT_8(M) REPEAT_8(M)
#define REPEAT_32(M) REPEAT_16(M) REPEAT_16(M)
#define REPEAT_64(M) REPEAT_32(M) REPEAT_32(M)
#define REPEAT_128(M) REPEAT_64(M) REPEAT_64(M)
#define REPEAT_256(M) REPEAT_128(M) REPEAT_128(M)

/* Standalone scaling probe for annotated terminal-break match dispatch. */
int32_t terminal_break_scale(int32_t x)
    _ensures(return == 0 || return == 1)
{
    int32_t result = 0;
    switch (x)
        _ensures(_live(x) && _live(result))
        _ensures(result == 0 || result == 1)
    {
#if SWITCH_SCALE_BRANCHES == 4
        REPEAT_4(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 8
        REPEAT_8(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 12
        REPEAT_8(SCALE_CASE)
        REPEAT_4(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 16
        REPEAT_16(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 24
        REPEAT_16(SCALE_CASE)
        REPEAT_8(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 32
        REPEAT_32(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 64
        REPEAT_64(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 128
        REPEAT_128(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 192
        REPEAT_128(SCALE_CASE)
        REPEAT_64(SCALE_CASE)
#elif SWITCH_SCALE_BRANCHES == 256
        REPEAT_256(SCALE_CASE)
#else
#error "Unsupported SWITCH_SCALE_BRANCHES value"
#endif
    }
    return result;
}

#undef REPEAT_256
#undef REPEAT_128
#undef REPEAT_64
#undef REPEAT_32
#undef REPEAT_16
#undef REPEAT_8
#undef REPEAT_4
#undef REPEAT_2
#undef SCALE_CASE
