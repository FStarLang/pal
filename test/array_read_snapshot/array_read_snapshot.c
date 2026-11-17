#include "pal.h"
#include <stdint.h>

/*
 * Reading from an array of structs, with a caller-supplied fact about every
 * element.
 *
 * The precondition quantifies over the array's value: every one of the first
 * `count` entries satisfies `entry_ok`. A C local initialized from the array,
 *
 *   entry_t entry = entries[i];
 *
 * is a direct read, and what is known about `entries[i]` carries over to the
 * local, so an assertion about the local alone can use the quantified fact.
 * The same holds when only a field is read: `entries[i].x`.
 */

typedef struct {
  uint32_t x;
} entry_t;

_let(bool entry_ok(entry_t e), e.x < 10)

/* Whole-struct read. The assertion mentions only the local `entry`. */
void read_struct_from_snapshot(_array entry_t *entries, uint32_t count)
  _preserves(entries._length == 64)
  _requires(count <= entries._length)
  _requires(_forall(size_t k, k < count ==> entry_ok(entries[k])))
{
  for (uint32_t i = 0; i < count; i = i + 1)
    _invariant(_live(i) && _live(count) && _live(*entries))
    _invariant(i <= count)
    _invariant(entries._length == 64 && count <= entries._length)
    _invariant(_forall(size_t k, k < count ==> entry_ok(entries[k])))
  {
    entry_t entry = entries[i];
    _assert(entry_ok(entry));
  }
}

/* Field read: the local `x` is the `x` field of the entry at `i`, so what is
   known about every entry is known about `x`. */
void read_field_from_snapshot(_array entry_t *entries, uint32_t count)
  _preserves(entries._length == 64)
  _requires(count <= entries._length)
  _requires(_forall(size_t k, k < count ==> entry_ok(entries[k])))
{
  for (uint32_t i = 0; i < count; i = i + 1)
    _invariant(_live(i) && _live(count) && _live(*entries))
    _invariant(i <= count)
    _invariant(entries._length == 64 && count <= entries._length)
    _invariant(_forall(size_t k, k < count ==> entry_ok(entries[k])))
  {
    uint32_t x = entries[i].x;
    _assert(x < 10);
  }
}
