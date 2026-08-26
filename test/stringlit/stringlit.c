#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

#define OBSERVE_MACRO_LITERALS()                                               \
    do {                                                                       \
        observe("macro-first");                                                \
        observe("macro-second");                                               \
    } while (0)

void write(const _array char *data, size_t nbytes)
    _requires(data._length == nbytes);

void observe(_plain const char *data);

void foo() {
    write("hello", 6);
}

void observe_string_literal() {
    observe("hello");
}

void write_compound_literal() {
    write((char[]){'o', 'k', '\0'}, 3);
}

void observe_compound_literal() {
    observe((char[]){'o', 'k', '\0'});
}

_plain const char *get_name()
    _ensures(return != NULL)
{
    return "hello";
}

_plain const char *get_indexed_name(uint32_t index)
    _ensures(return != NULL)
{
    switch (index) {
    case 0:
        return "zero";
    case 1:
        return "one";
    default:
        return "other";
    }
}

void observe_macro_literals() {
    OBSERVE_MACRO_LITERALS();
}
