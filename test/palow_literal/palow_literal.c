#include "pal.h"
#include <stdlib.h>

void observe_literal(const _array char *fmt)
    _requires(fmt._length > 1 && fmt[0] == 'h');

void observe_any(const _array char *fmt)
    _requires(fmt._length > 1);

void call_literal(void) {
    observe_literal("hi");
}


void call_local_array(void) {
    char buf[] = "hi";
    observe_any(buf);
}

void call_heap_array(void) {
    char *buf = (char *) calloc(3, sizeof(char));
    if (buf == NULL) {
        return;
    }
    observe_any(buf);
    free(buf);
}

void forward_const_array(const _array char *s)
    _requires(s._length > 1 && s[0] == 'h')
{
    observe_literal(s);
}

void call_forward_const_array(void) {
    forward_const_array("hi");
}

void read_literal_body(const _array char *s)
    _requires(s._length > 1 && s[0] == 'h')
{
    char h = s[0];
    _assert(h == 'h');
}

void call_read_literal_body(void) {
    read_literal_body("hi");
}

void call_literal_twice(void) {
    observe_literal("hi");
    observe_literal("hi");
}

void observe_mut(_array char *buf)
    _requires(buf._length == 3)
{
    buf[0] = 'H';
}

void mutable_literal_still_copies(void) {
    observe_mut((char[]){'h', 'i', '\0'});
}

/* Expected to fail if enabled: first byte is not 'h'.
void bad_literal(void) {
    observe_literal("no");
}
*/
