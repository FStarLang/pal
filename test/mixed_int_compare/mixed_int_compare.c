#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

bool compare_u32_u64(uint32_t i, uint64_t j) {
    if (i < j) {
        return true;
    } else {
        return false;
    }
}

bool compare_u64_u32(uint64_t i, uint32_t j) {
    if (i < j) {
        return true;
    } else {
        return false;
    }
}
