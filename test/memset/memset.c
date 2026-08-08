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

// A platform wrapper around memset. Declaring it `_memset_zero` says that a
// call `f(ptr, size)` is the zero fill, so calls translate to the same
// whole-object write as a direct memset rather than to an uninterpreted stub.
_memset_zero
void plat_zero(void *buffer, size_t size);

void zero_triple_via_wrapper(struct triple *s)
    _ensures(s->a == 0)
    _ensures(s->c == 0)
{
    plat_zero(s, sizeof(*s));
}

// The wrapper composes with a later field write, exactly as memset does: the
// field written afterwards holds its new value and the untouched ones are 0.
void zero_then_set(struct triple *s)
    _ensures(s->a == 7)
    _ensures(s->b == 0)
{
    plat_zero(s, sizeof(struct triple));
    s->a = 7;
}

// Zeroing a local through the wrapper, matching `zero_local` above.
int zero_local_via_wrapper(void)
    _ensures(return == 0)
{
    struct triple t;
    plat_zero(&t, sizeof(t));
    return t.a;
}
