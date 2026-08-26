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

/* A local array with an initializer is allocated correctly and its length is
   inferred correctly, but the initializer assigns the array *spec* into the
   variable instead of writing the contents into the array just allocated:
   `var_buf := array_spec_of_list_with_len ..`. F* reports Error 19.

   The call position is irrelevant -- the failure is at the declaration -- so
   one call site suffices. Note this breaks statement position, which `foo`
   above shows working when the literal is passed inline. */

void init_from_string(void) {
    char buf[] = "lo";
    write(buf, 3);
}

/* A brace initializer instead of a string literal: the elements are emitted
   through an int32->int8 cast rather than directly, so it is covered too. */
void init_from_braces(void) {
    char buf[3] = {'o', 'k', '\0'};
    write(buf, 3);
}

