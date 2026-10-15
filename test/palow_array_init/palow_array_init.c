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
