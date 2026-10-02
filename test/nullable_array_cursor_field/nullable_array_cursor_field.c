#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef struct Entry {
  uint32_t value;
} Entry;

_include_pulse(CursorField,
  [@@pulse_eager_unfold]
  let cursor_payload (cur: array $type(Entry)) (base: array $type(Entry))
      (remaining: nat) (capacity: nat) =
    arrayptr_pts_to cur base **
    pure (offset_of base <= offset_of cur /\ offset_of cur + remaining <= offset_of base + capacity)

  [@@pulse_eager_unfold]
  let cursor_remaining (cur: array $type(Entry)) (base: array $type(Entry))
      (remaining: nat) (capacity: nat) =
    Pulse.Lib.C.Nullable.unless_null cur (cursor_payload cur base remaining capacity)

  ghost fn open_cursor (cur: array $type(Entry)) (base: array $type(Entry))
      (remaining: nat) (capacity: nat)
    requires cursor_remaining cur base remaining capacity
    requires pure (not (Pulse.Lib.C.Nullable.test_null #(array $type(Entry)) cur))
    ensures cursor_payload cur base remaining capacity
  {
    Pulse.Lib.C.Nullable.elim_unless_null_arr #$type(Entry) cur #(cursor_payload cur base remaining capacity);
  }

  ghost fn close_cursor (cur: array $type(Entry)) (base: array $type(Entry))
      (remaining: nat) (capacity: nat)
    requires cursor_payload cur base remaining capacity
    ensures cursor_remaining cur base remaining capacity
  {
    Pulse.Lib.C.Nullable.intro_unless_null_array #$type(Entry) cur (cursor_payload cur base remaining capacity);
  }

  ghost fn drop_empty_cursor (cur: array $type(Entry)) (base: array $type(Entry))
      (capacity: nat)
    requires cursor_remaining cur base 0 capacity
  {
    if (Pulse.Lib.C.Nullable.test_null #(array $type(Entry)) cur) {
      Pulse.Lib.C.Nullable.elim_null_arr #$type(Entry) cur #(cursor_payload cur base 0 capacity);
    } else {
      Pulse.Lib.C.Nullable.elim_unless_null_arr #$type(Entry) cur #(cursor_payload cur base 0 capacity);
      arrayptr_drop cur;
    }
  }
)

typedef struct Message {
  _arrayptr Entry *next;
} Message;

void write_and_advance(Message *message, Entry value, size_t remaining, size_t capacity)
  _requires(_inline_pulse(array_pts_to_full $`arr 1.0R $`cells))
  _requires(remaining > 0)
  _requires((bool) _inline_pulse(SizeT.v $(capacity) <= array_spec_len $`cells))
  _requires(_inline_pulse(CursorField.cursor_remaining $(message->next) $`arr (SizeT.v $(remaining)) (SizeT.v $(capacity))))
  _ensures(_inline_pulse(exists* cells1. array_pts_to_full $`arr 1.0R cells1 **
    pure (array_spec_len cells1 == array_spec_len $`cells) **
    CursorField.cursor_remaining $(message->next) $`arr (SizeT.v $(remaining) - 1) (SizeT.v $(capacity))))
{
  if (message->next != NULL) {
    _ghost_stmt(CursorField.open_cursor $(message->next) $`arr (SizeT.v $(remaining)) (SizeT.v $(capacity)));
    *message->next = value;
    message->next++;
    _ghost_stmt(CursorField.close_cursor $(message->next) $`arr (SizeT.v $(remaining) - 1) (SizeT.v $(capacity)));
  } else {
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_null_arr #$type(Entry) $(message->next) #(CursorField.cursor_payload $(message->next) $`arr (SizeT.v $(remaining)) (SizeT.v $(capacity))));
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null_array #$type(Entry) $(message->next) (CursorField.cursor_payload $(message->next) $`arr (SizeT.v $(remaining) - 1) (SizeT.v $(capacity))));
  }
}

void fill_all(_array Entry *out, size_t n)
  _requires(out._length == n)
  _preserves_value(out._length)
{
  Message message = { .next = out };
  _arrayptr Entry *cur = out;
  Entry e = { .value = 7 };
  size_t remaining = n;
  _ghost_stmt(CursorField.close_cursor $(cur) $(out) (SizeT.v $(n)) (SizeT.v $(n)));
  while (remaining > 0)
    _invariant(_live(remaining) && _live(n) && _live(message.next) && _live(cur))
    _invariant(remaining <= n)
    _invariant(out._length == n)
    _invariant(_inline_pulse(exists* cells_cur. array_pts_to_full $(out) 1.0R cells_cur **
      pure (array_spec_len cells_cur == SizeT.v $(n)) **
      CursorField.cursor_remaining $(cur) $(out) (SizeT.v $(remaining)) (SizeT.v $(n))))
  {
    size_t next_remaining = remaining - 1;
    message.next = cur;
    write_and_advance(&message, e, remaining, n);
    _ghost_stmt(Struct_Message.struct_message__aux_raw_unfold $(&message) $(message));
    cur = message.next;
    _ghost_stmt(rewrite
      (CursorField.cursor_remaining $(cur) $(out) (SizeT.v $(remaining) - 1) (SizeT.v $(n)))
      as
      (CursorField.cursor_remaining $(cur) $(out) (SizeT.v $(next_remaining)) (SizeT.v $(n))));
    remaining = next_remaining;
  }
  _assert(remaining == 0);
  _assert(out._length == n);
  _ghost_stmt(rewrite
    (CursorField.cursor_remaining $(cur) $(out) (SizeT.v $(remaining)) (SizeT.v $(n)))
    as
    (CursorField.cursor_remaining $(cur) $(out) 0 (SizeT.v $(n))));
  _ghost_stmt(CursorField.drop_empty_cursor $(cur) $(out) (SizeT.v $(n)));
}


void skip_null_cursor(_array Entry *out, size_t n)
  _requires(out._length == n)
  _preserves_value(out._length)
{
  Message message = { .next = NULL };
  _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null_array #$type(Entry) $(message.next) (CursorField.cursor_payload $(message.next) $(out) (SizeT.v $(n)) (SizeT.v $(n))));
  _ghost_stmt(Pulse.Lib.C.Nullable.elim_null_arr #$type(Entry) $(message.next) #(CursorField.cursor_payload $(message.next) $(out) (SizeT.v $(n)) (SizeT.v $(n))));
}

typedef struct CursorBox {
  _arrayptr Entry *next;
} CursorBox;

void arrayptr_field_arithmetic(_array Entry *out)
  _requires(out._length == 4)
  _preserves_value(out._length)
{
  CursorBox box = { .next = out };
  _arrayptr Entry *old = box.next++;
  box.next += 1;
  box.next = box.next + 1;
  _ghost_stmt(arrayptr_drop $(old));
  _ghost_stmt(arrayptr_drop $(box.next));
}
