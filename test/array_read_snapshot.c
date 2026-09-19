#include "pal.h"
#include <stdint.h>

/*
 * Regression test for preserving the logical snapshot fact produced by
 * Pulse.Lib.C.Array.array_read.
 *
 * PAL models an _array value with the ghost snapshot
 *
 *   array_value_of entries : Seq.seq (option entry_t)
 *
 * and array_read proves that the concrete value read at index i rewrites to
 *
 *   Some?.v (Seq.index (array_value_of entries) i)
 *
 * provided the array element exists. This regression records that PAL's
 * ordinary translation of a C local initialization such as
 *
 *   entry_t entry = entries[i];
 *
 * as a direct read into the mutable local is strong enough: the array_read
 * postcondition remains available through the assignment, so a ghost assertion
 * about entry can use a precondition quantified over array_value_of entries.
 *
 * The key point is that no special emitter machinery is needed here: PAL should
 * neither introduce a second read temporary nor emit an extra pure equality
 * assertion. These tests exercise both whole-struct reads and field reads, and
 * fail if the direct array_read assignment loses the snapshot refinement.
 */

typedef struct {
  uint32_t x;
} entry_t;

_include_pulse(
  $declare(entry_t e)

  let entry_ok ($(e): $type(entry_t)) : prop =
    UInt32.v $(e.x) < 10

  // Specification supplied by the caller: every initialized entry in the first
  // n array slots satisfies entry_ok. The proof obligations below are about
  // concrete locals read from entries[i], so they require PAL to expose the
  // connection between those locals and this ghost snapshot.
  let entries_ok (s: Seq.seq (option $type(entry_t))) (n: nat) : prop =
    forall i. i < n ==> Some? (Seq.index s i) ==>
      entry_ok (Some?.v (Seq.index s i))
)

/*
 * Whole-struct read case.
 *
 * The assertion after the read intentionally mentions only the concrete local
 * entry. It does not restate the Seq.index expression; the proof relies on the
 * ordinary array_read assignment preserving enough information to connect entry
 * back to array_value_of entries.
 */
void read_struct_from_snapshot(
    _refine(this._length == 64) _array entry_t *entries,
    uint32_t count)
  _requires(count <= entries._length)
  _requires((bool) _inline_pulse(
    entries_ok (array_value_of $(entries)) (UInt32.v $(count))))
{
  for (uint32_t i = 0; i < count; i = i + 1)
    _invariant(_live(i) && _live(count))
    _invariant(i <= count)
    _invariant(count <= entries._length)
    _invariant((bool) _inline_pulse(
      entries_ok (array_value_of $(entries)) (UInt32.v $(count))))
  {
    entry_t entry = entries[i];
    _ghost_stmt(assert pure (entry_ok $(entry)));
  }
}

/*
 * Field-read case.
 *
 * C code often reads only a field of an array element, e.g. entries[i].x. The
 * same snapshot fact must be available after projection: the local x should be
 * known equal to the x field of the snapshot entry at i.
 */
void read_field_from_snapshot(
    _refine(this._length == 64) _array entry_t *entries,
    uint32_t count)
  _requires(count <= entries._length)
  _requires((bool) _inline_pulse(
    entries_ok (array_value_of $(entries)) (UInt32.v $(count))))
{
  for (uint32_t i = 0; i < count; i = i + 1)
    _invariant(_live(i) && _live(count))
    _invariant(i <= count)
    _invariant(count <= entries._length)
    _invariant((bool) _inline_pulse(
      entries_ok (array_value_of $(entries)) (UInt32.v $(count))))
  {
    uint32_t x = entries[i].x;
    _ghost_stmt(assert pure (UInt32.v $(x) < 10));
  }
}
