#include "pal.h"
#include <stdlib.h>

void write(const _array char *data, size_t nbytes)
    _requires(data._length == nbytes);

void observe(_plain const char *data);

void foo() {
    write("hello", 6);
}

void write_compound_literal() {
    write((char[]){'o', 'k', '\0'}, 3);
}

void observe_compound_literal() {
    observe((char[]){'o', 'k', '\0'});
}

_plain const char *get_name() {
    return "hello";
}
