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

void fresh_group(_plain struct group *p)
    _requires(_inline_pulse(struct_group_pts_to_uninit $(p)))
    _ensures(_inline_pulse(exists* g. struct_group_pts_to $(p) 1.0R g **
        pure (g.fld_tag == 9ul
              /\ (FStar.Seq.index g.fld_entries 0).fld_count == 3ul
              /\ Union_word.union_word_repr (Union_word.Union_word_bits 13UL)
                   (FStar.Seq.index g.fld_entries 0).fld_saved
              /\ (FStar.Seq.index g.fld_entries 1).fld_count == 0ul)))
{
    _ghost_stmt($unfold-uninit(struct group) $(p));
    *p = (struct group){ .tag = 9, .entries = {{ .count = 3, .saved.bits = 13 }} };
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
