#include "pal.h"
#include <stdint.h>

struct flags {
    unsigned int a : 3;  // value in [0, 8)
    unsigned int b : 5;  // value in [0, 32)
    unsigned int full;   // ordinary (non-bit-field) member
};

// Read a bit-field through a pointer.
unsigned int read_a(struct flags *s)
  _ensures(return == s->a)
{
    return s->a;
}

// Read a bit-field by value.
unsigned int read_b_by_value(_plain struct flags s)
  _ensures(return == s.b)
{
    return s.b;
}

// Read an ordinary member alongside bit-fields.
unsigned int read_full(struct flags *s)
  _ensures(return == s->full)
{
    return s->full;
}

// Writing an arbitrary value to a 3-bit field: the write masks the RHS to
// 3 bits (C unsigned modular truncation), so `s->a` ends up holding `v % 8`.
// Without masking this would violate the cell's `< pow2 3` refinement.
void write_a(struct flags *s, unsigned int v)
  _ensures(s->a == v % 8)
{
    s->a = v;
}

// Writing an in-range constant stores it unchanged.
void set_a(struct flags *s)
  _ensures(s->a == 5)
{
    s->a = 5;
}

// A _Bool bit-field of width 1. `_Bool` is an unsigned type so the frontend
// accepts it, but it is modeled as a plain F* `bool` (already a 1-bit value):
// no `< pow2 n` refinement and no write masking are needed.
struct bits {
    _Bool flag : 1;
    unsigned char nibble : 4;
};

// Read a _Bool bit-field.
_Bool read_flag(struct bits *s)
  _ensures(return == s->flag)
{
    return s->flag;
}

// Write a _Bool bit-field: a `_Bool` already holds only 0/1, so the value is
// stored unchanged (no truncation).
void write_flag(struct bits *s, _Bool v)
  _ensures(s->flag == v)
{
    s->flag = v;
}

unsigned char read_nibble(struct bits *s)
  _ensures(return == s->nibble)
{
    return s->nibble;
}

unsigned char read_loaned_nibble(_plain const struct bits *s)
  _ghost_arg(unsigned char storage)
  _preserves(_inline_pulse(uint8_t_pts_to ($(s) +! Struct_bits.struct_bits_offsetof_bits0) 0.5R $(storage)))
  _ensures(_inline_pulse(pure ($(return) == Pulse.Lib.C.Palow.Bits.get8 $(storage) 1 4)))
{
    return s->nibble;
}

void write_nibble(struct bits *s, unsigned char v)
  _ensures(s->nibble == v % 16)
{
    s->nibble = v;
}

struct bits init_bits(_Bool flag, unsigned char value)
  _ensures(return.flag == flag && return.nibble == value % 16)
{
    return (struct bits){ .flag = flag, .nibble = value };
}

struct bits init_flag(_Bool flag)
  _ensures(return.flag == flag && return.nibble == 0)
{
    return (struct bits){ .flag = flag };
}

// A bit-field whose declared type is a typedef (`uint16_t` = unsigned short).
// The typedef must be resolved to its underlying machine width so the cell
// still carries the `< pow2 n` refinement.
struct tdef {
    uint16_t a : 2;  // value in [0, 4)
};

// The refinement on the typedef'd cell lets us prove the range on read
// (regression test for the reported typedef bit-field bug).
void tdef_in_range(struct tdef *s)
{
    _assert(s->a <= 3);
}

uint16_t read_tdef(struct tdef *s)
  _ensures(return == s->a)
{
    return s->a;
}

void write_tdef(struct tdef *s, uint16_t v)
  _ensures(s->a == v % 4)
{
    s->a = v;
}

// Keep a Boolean-to-integer store across a later short-circuit join.
struct table_header {
    uint32_t length;
    uint8_t encoding;
};

_Bool write_bool_before_join(struct bits *s, struct table_header *header)
  _ensures(s->nibble == (header->length > 0 ? 1 : 0))
{
    s->nibble = (header->length > 0);
    return header->encoding != 0 && header->encoding != 2;
}

_Bool convert_bool_before_join(int64_t *value, _Bool flag, struct table_header *header)
  _ensures(*value == (flag ? 1L : 0L))
{
    *value = flag;
    return header->encoding != 0 && header->encoding != 2;
}

typedef union _overlay {
    struct {
        uint16_t prefix;
        uint8_t neighbor : 3;
        uint8_t flag : 1;
    } view;
    uint8_t bytes[4];
} packed_view;

/* Only the bit-field storage unit is readable, not the enclosing arm. */
void mark_overlay_bit(packed_view *p)
    _requires(_inline_pulse(pure (Pulse.Lib.C.Palow.Pun.plain (slice $(*p) 2 3))))
    _ensures(_inline_pulse(pure ($(*p) == Pulse.Lib.C.Palow.Pun.overlay $(_old(*p)) 0
        (Pulse.Lib.C.Palow.Pun.uint8_t_bytes (Bits.put8
            (Pulse.Lib.C.Palow.Pun.uint8_t_of_bytes (slice $(_old(*p)) 2 3)) 3 1 1uy)) 2)))
{
    p->view.flag = 1;
}

uint8_t read_overlay_neighbor(const packed_view *p)
    _requires(_inline_pulse(pure (Pulse.Lib.C.Palow.Pun.plain (slice $(*p) 2 3))))
    _ensures(_inline_pulse(pure ($(return) == Bits.get8
        (Pulse.Lib.C.Palow.Pun.uint8_t_of_bytes (slice $(*p) 2 3)) 0 3)))
{
    return p->view.neighbor;
}
