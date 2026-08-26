#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// ===========================================================================
// `_array` / `_arrayptr` through a pointer typedef.
//
// C codebases commonly name pointers with a typedef (`typedef E* PE;`). The
// pointer-kind attributes classify the *pointer*, so PAL desugars a typedef
// that resolves to a pointer before applying them. Without that, `PE` is an
// opaque type reference and the attribute has nothing to attach to.
// ===========================================================================

typedef struct _E
{
    uint16_t a;
    uint16_t b;
} E;

typedef E* PE;
typedef const E* PCE;

// The classic bounds-checked table accessor: the caller owns `table`, the
// index is in bounds, and the result is a live pointer to cell `idx`.
_arrayptr PE get_entry(_array PE table, uint32_t count, uint32_t idx)
  _requires(table._length == count && idx < count)
  _ensures(_inline_pulse(
      arrayptr_pts_to $(return) $(table) **
      pure (offset_of $(return) == offset_of $(table) + FStar.UInt32.v $(idx))))
{
    _arrayptr PE entry = NULL;

    entry = &table[idx];

    return entry;
}

// The same desugaring applies to a const-qualified pointer typedef.
uint16_t read_first(_array PCE table)
  _requires(table._length > 0)
{
    return table[0].a;
}
