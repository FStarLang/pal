#include "pal.h"
#include <stdint.h>
#include <string.h>

// Zero a byte array; variable element count.
void zero_bytes(uint8_t a[], size_t n)
    _requires(a._length == n)
{
    memset(a, 0, n * sizeof(uint8_t));
}

// The zero fill is observable: every cell holds 0 afterwards.
void zero_const(uint8_t a[])
    _requires(a._length == 4)
    _preserves_value(a._length)
    _ensures(a[0] == 0)
{
    memset(a, 0, sizeof(uint8_t) * 4);
}

// char arrays are also byte-sized and supported.
void zero_char(char a[])
    _requires(a._length == 4)
    _preserves_value(a._length)
    _ensures(a[0] == 0)
{
    memset(a, 0, sizeof(char) * 4);
}

struct triple {
    int a;
    int b;
    int c;
};

// Zeroing a whole struct through a pointer: memset(ptr, 0, sizeof(T)) is
// supported for any type (here a 3-field struct), emitted as a whole-object
// write of `zero_default`.
void zero_triple(struct triple *s)
    _ensures(s->a == 0)
{
    memset(s, 0, sizeof(struct triple));
}

struct withbuf {
    int buf[4];
    int x;
};

// Zeroing a struct that contains an inline (fixed-size) array; both the
// scalar field and the array cells are observably zero afterwards.
void zero_withbuf(struct withbuf *s)
    _ensures(s->x == 0)
    _ensures(s->buf[0] == 0)
{
    memset(s, 0, sizeof(struct withbuf));
}

// Zeroing a single local struct via address-of (memset(&s, 0, sizeof(s)));
// the zeroed field is observable through the return value.
int zero_local(void)
    _ensures(return == 0)
{
    struct triple t;
    memset(&t, 0, sizeof(t));
    return t.a;
}
