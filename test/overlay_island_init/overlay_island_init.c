#include "pal.h"
#include <stdint.h>

typedef union word {
    struct { int32_t lo; uint32_t hi; };
    uint64_t bits;
} word;

struct entry { uint32_t count; word saved; };
union _overlay view { struct entry entry; uint64_t prefix; };
struct group { uint32_t tag; struct entry entries[2]; };

word reset(struct entry *p)
    _ensures(p->count == 7)
    _ensures(_inline_pulse(pure (Union_word.union_word_repr
        (Union_word.Union_word__unnamed0 { fld_lo = 0l; fld_hi = 0ul }) $(p->saved))))
{
    *p = (struct entry){ .count = 7 };
    return p->saved;
}

word reset_group(struct group *p)
    _ensures(p->tag == 0 && p->entries[1].count == 0)
{
    *p = (struct group){0};
    return p->entries[1].saved;
}

word replace(union view *p, int32_t lo)
    _ensures(_inline_pulse(pure (Union_word.union_word_repr
        (Union_word.Union_word__unnamed0 { fld_lo = $(lo); fld_hi = 0ul }) $(p->entry.saved))))
{
    p->entry = (struct entry){ .saved = { .lo = lo } };
    return p->entry.saved;
}

void save_count(struct entry *p)
    _ensures(p->count == 0)
    _ensures(_inline_pulse(pure (Union_word.union_word_repr
        (Union_word.Union_word__unnamed0 { fld_lo = 0l; fld_hi = $(_old(p->count)) }) $(p->saved))))
{
    *p = (struct entry){ .saved = { .hi = p->count } };
}

void set_bits(struct entry *p, uint64_t bits)
    _ensures(_inline_pulse(pure (Union_word.union_word_repr
        (Union_word.Union_word_bits $(bits)) $(p->saved))))
{
    *p = (struct entry){ .saved = { .bits = bits } };
}
