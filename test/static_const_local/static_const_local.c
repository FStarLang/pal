#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* A block-scope `static const` with an initializer holds the same value on
   every call, so PAL translates it as a local initialized on each call. */
uint32_t lookup(size_t i) _requires(i < 3) _ensures(return == 10 * (i + 1)) {
    static const uint32_t table[] = {10, 20, 30};
    return table[i];
}

typedef struct {
    uint32_t offset;
    uint32_t kind;
} entry;

uint32_t second_kind(void) _ensures(return == 7) {
    static const entry entries[] = {
        {.offset = 0, .kind = 5},
        {.offset = 8, .kind = 7},
    };
    return entries[1].kind;
}

/* Only the value of a scalar `static const` is used. */
uint32_t scaled(uint32_t x) _requires(x < 1000) _ensures(return == 4 * x) {
    static const uint32_t factor = 4;
    return factor * x;
}

/* `sizeof(*(a))` decays the array, but only in an unevaluated operand. */
#define ARRAY_SIZE(x) (sizeof(x) / sizeof(*(x)))

size_t entry_count(void) _ensures(return == 2) {
    static const entry entries[] = {
        {.offset = 0, .kind = 5},
        {.offset = 8, .kind = 7},
    };
    return ARRAY_SIZE(entries);
}
