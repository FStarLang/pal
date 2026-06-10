#include "pal.h"
#include <stdlib.h>

void write(const _array char *data, size_t nbytes)
    _requires(data._length == nbytes);

void foo() {
    write("hello", 6);
}