#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

void write(const _array char *data, size_t nbytes)
    _requires(data._length == nbytes);

void sink(_plain const char *data);

void f(void) {
    char buf[6] = "hello";
    int xs[4] = {1, 2, 3};

    _assert(buf[1] == 'e');
    _assert(xs[3] == 0);
    sink(buf);
    write(buf, 6);
}

struct array_record {
    uint32_t tag;
    uint8_t bytes[4];
};

int zero_record_array(void) _ensures(return == 0) {
    struct array_record r = {0};
    return r.bytes[0] + r.bytes[3];
}

uint32_t partial_record_array(void) _ensures(return == 7) {
    struct array_record r = {.tag = 7};
    return r.tag + r.bytes[2];
}

struct matrix_record {
    uint8_t marker;
    uint16_t grid[2][3];
};

int zero_record_matrix(void) _ensures(return == 5) {
    struct matrix_record r = {.marker = 5};
    return r.marker + r.grid[0][2] + r.grid[1][2];
}
