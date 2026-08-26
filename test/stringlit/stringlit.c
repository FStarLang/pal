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

/* A local array with an initializer writes its contents into the array just
   allocated, via array_multiple_writes. */
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

