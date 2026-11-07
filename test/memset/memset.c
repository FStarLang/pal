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

void zero_out(_out uint8_t a[], size_t n)
    _requires(a._length == n && n > 0)
    _ensures(a[0] == 0)
{
    memset(a, 0, n * sizeof(uint8_t));
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

void zero_inline_array(struct withbuf *s)
    _ensures(s->buf[0] == 0)
    _ensures(s->buf[3] == 0)
    _ensures(s->x == _old(s->x))
{
    memset(s->buf, 0, sizeof(s->buf));
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

struct bytebuf {
    uint8_t buf[5];
    int x;
};

void zero_buffer_field(struct bytebuf *s)
    _requires(_inline_pulse(pure (FStar.Int32.v $(s->x) == 42)))
    _ensures(s->buf[0] == 0 && s->buf[4] == 0)
    _preserves_value(s->x)
{
    memset(s->buf, 0, sizeof(s->buf));
}

void initialize_buffer_field(_out struct bytebuf *s, int tag)
    _requires(_inline_pulse(pure (FStar.Int32.v $(tag) == 42)))
    _ensures(s->x == 42)
    _ensures(s->buf[0] == 0 && s->buf[4] == 0)
{
    s->x = tag;
    plat_zero(s->buf, sizeof(s->buf));
}

void initialize_array_first(_out struct bytebuf *s, int tag)
    _requires(_inline_pulse(pure (FStar.Int32.v $(tag) == 42)))
    _ensures(s->x == 42)
    _ensures(s->buf[0] == 0 && s->buf[4] == 0)
{
    plat_zero(s->buf, sizeof(s->buf));
    s->x = tag;
}

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

struct fill_flags {
    uint8_t enabled : 1;
    uint8_t reserved : 7;
};

struct fill_record {
    uint64_t offset;
    uint8_t state;
    struct fill_flags flags;
    uint32_t count;
};

uint32_t last_count(const struct fill_record records[])
    _requires(records._length == 2)
    _ensures(return == records[1].count)
{
    return records[1].count;
}

uint32_t paint_records(void)
    _ensures(return == UINT32_MAX)
{
    struct fill_record records[2] = {0};
    memset(records, 0xFF, sizeof(records));
    _assert(records[0].offset == UINT64_MAX);
    _assert(records[0].state == UINT8_MAX);
    _assert(records[0].flags.enabled == 1);
    _assert(records[1].flags.reserved == 127);
    return last_count(records);
}

uint32_t paint_uninitialized_words(void)
    _ensures(return == 0x01010101)
{
    uint32_t words[3];
    memset(words, 0x101, sizeof(words));
    _assert(words[0] == 0x01010101);
    return words[2];
}

uint16_t repaint_words(void)
    _ensures(return == 0xA5A5)
{
    uint16_t words[2] = {1, 2};
    memset(words, -1, sizeof(words));
    _assert(words[1] == UINT16_MAX);
    memset(words, 0xA5, sizeof(words));
    return words[0];
}

void paint_bytes(uint8_t bytes[])
    _requires(bytes._length == 4)
    _preserves_value(bytes._length)
    _ensures(bytes[0] == 0xAB && bytes[3] == 0xAB)
{
    memset(bytes, 0xAB, sizeof(uint8_t) * 4);
}

void paint_empty(uint8_t bytes[])
    _requires(bytes._length == 0)
    _preserves_value(bytes._length)
{
    memset(bytes, 0xFF, sizeof(uint8_t) * 0);
}

uint8_t first_byte(const uint8_t bytes[])
    _requires(bytes._length == 4)
    _ensures(return == bytes[0])
{
    return bytes[0];
}

uint8_t zero_initialized_bytes(void)
    _ensures(return == 0)
{
    uint8_t bytes[4] = {1, 2, 3, 4};
    memset(bytes, 0, sizeof(bytes));
    return first_byte(bytes);
}
