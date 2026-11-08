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

/* A local array with a constant initializer is emitted as one Palow array-fill
   call whose post-state is the constant sequence. */
void init_from_string(void) {
    char buf[] = "lo";
    write(buf, 3);
}

/* A brace initializer instead of a string literal: the elements are emitted
   through an int32->int8 cast rather than directly, so it is covered too. */
void init_from_braces(void) {
    char buf[3] = {'o', 'k', '\0'};
    _assert(buf[0] == 'o');
    write(buf, 3);
}

/* A string shorter than the array: the initializer is padded with NULs up to
   the declared length, so every cell is written and the length is 8, not 3. */
void init_shorter_string(void) {
    char buf[8] = "lo";
    _assert(buf[0] == 'l');
    _assert(buf[5] == '\0');
    write(buf, 8);
}

/* Not supported: truncating a string literal to drop its NUL. This is legal C,
   but the literal elaborates at its natural length and PAL has no truncating
   array-to-array cast --
     error: unsupported cast from int8_t[3] to int8_t[2]

void init_truncated(void) {
    char buf[2] = "lo";
    write(buf, 2);
}
*/


/* `__func__` is a string literal holding the function name, NUL included. */
void name_sink(const _array char *name)
    _requires(name._length == 10);

void func_name(void) {
    name_sink(__func__);
}
