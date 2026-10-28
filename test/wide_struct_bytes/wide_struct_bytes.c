#include "pal.h"
#include <stdint.h>

/* A 32-field record with inter-field and trailing padding. */
struct wide_record {
  uint8_t first;
  uint32_t v00, v01, v02, v03, v04, v05, v06, v07, v08, v09;
  uint32_t v10, v11, v12, v13, v14, v15, v16, v17, v18, v19;
  uint32_t v20, v21, v22, v23, v24, v25, v26, v27, v28, v29;
  uint8_t last;
};

union wide_union {
  struct wide_record record;
  uint64_t scalar;
};

union wide_union make_wide(uint32_t value)
  _ensures(return.record._active)
  _ensures(return.record.first == 1)
  _ensures(return.record.v29 == value)
  _ensures(return.record.last == 2)
{
  union wide_union u = {
    .record = { .first = 1, .v29 = value, .last = 2 }
  };
  return u;
}

void set_last(union wide_union *u, uint32_t value)
  _requires(u->record._active)
  _ensures(u->record._active)
  _ensures(u->record.v29 == value)
{
  u->record.v29 = value;
}

uint32_t array_last(_array const struct wide_record *values)
  _requires(values._length == 2)
  _ensures(return == values[1].v29)
{
  return values[1].v29;
}
