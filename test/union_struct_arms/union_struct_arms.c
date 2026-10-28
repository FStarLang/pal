#include "pal.h"
#include <stdint.h>

/* Unions whose members are structs, including structs with array fields and
 * unions nested as members of other unions. */

struct reading {
  uint8_t sensor[4];
  int32_t value;
};

struct stats {
  uint16_t samples;
  uint16_t dropped;
};

union record {
  struct reading rd;
  struct stats st;
};

/* A union whose member is itself a union of structs. */
struct alarm {
  uint64_t raised_at;
  uint8_t level;
};

union event {
  union record rec;
  struct alarm al;
};

_include_pulse(RecordTags,
  let is_reading (r: Union_record.union_record) : prop =
    Union_record.Union_record_rd? r
)

int32_t reading_value_from_pure_contract(const union record *r)
  _requires((_Bool)_inline_pulse(RecordTags.is_reading $(*r)))
  _ensures(return == r->rd.value)
{
  return r->rd.value;
}

/* Reading a field of the live arm, including an element of an array field. */
int32_t reading_value(union record *r)
  _requires(r->rd._active)
  _ensures(r->rd._active)
  _ensures(return == r->rd.value)
{
  return r->rd.value;
}

uint8_t first_sensor(union record *r)
  _requires(r->rd._active)
  _ensures(r->rd._active)
  _ensures(return == r->rd.sensor[0])
{
  return r->rd.sensor[0];
}

/* Writing fields of the live arm in place. */
void count_sample(union record *r, uint16_t dropped)
  _requires(r->st._active)
  _requires(r->st.samples < 1000)
  _ensures(r->st._active)
  _ensures(r->st.samples == _old(r->st.samples) + 1)
  _ensures(r->st.dropped == dropped)
{
  r->st.samples = r->st.samples + 1;
  r->st.dropped = dropped;
}

void tag_sensor(union record *r, uint8_t id)
  _requires(r->rd._active)
  _ensures(r->rd._active)
  _ensures(r->rd.sensor[2] == id)
  _ensures(r->rd.value == _old(r->rd.value))
{
  r->rd.sensor[2] = id;
}

/* A function that knows only the struct. */
uint32_t stats_total(const struct stats *s)
  _ensures(return == (uint32_t)s->samples + (uint32_t)s->dropped)
{
  return (uint32_t)s->samples + (uint32_t)s->dropped;
}

void stats_reset(_out struct stats *s)
  _ensures(s->samples == 0 && s->dropped == 0)
{
  s->samples = 0;
  s->dropped = 0;
}

/* Handing the live arm to a function that knows only the struct. */
uint32_t record_total(union record *r)
  _requires(r->st._active)
  _ensures(r->st._active)
  _ensures(return == (uint32_t)r->st.samples + (uint32_t)r->st.dropped)
{
  return stats_total(&r->st);
}

/* Handing an arm to an `_out` function makes it the live one, whatever was
 * live before. */
void record_reset(union record *r)
  _ensures(r->st._active)
  _ensures(r->st.samples == 0)
{
  stats_reset(&r->st);
}

/* Making an arm live by writing it as a whole. */
void record_set_stats(union record *r, struct stats s)
  _ensures(r->st._active)
  _ensures(r->st.dropped == s.dropped)
{
  r->st = s;
}

/* Two levels: an arm of an arm. */
int32_t event_value(union event *e)
  _requires(e->rec._active && e->rec.rd._active)
  _ensures(e->rec._active && e->rec.rd._active)
  _ensures(return == e->rec.rd.value)
{
  return e->rec.rd.value;
}

void event_bump_level(union event *e)
  _requires(e->al._active)
  _requires(e->al.level < 9)
  _ensures(e->al._active)
  _ensures(e->al.level == _old(e->al.level) + 1)
{
  e->al.level = e->al.level + 1;
}

/* An inner union handed on as itself. */
int32_t event_record_value(union event *e)
  _requires(e->rec._active && e->rec.rd._active)
  _ensures(e->rec._active && e->rec.rd._active)
{
  return reading_value(&e->rec);
}

/* A local union, filled through one arm and read back through it. */
uint32_t local_stats(void)
  _ensures(return == 7)
{
  union record r;
  r.st.samples = 5;
  r.st.dropped = 2;
  return stats_total(&r.st);
}

/* A struct with an array field now has a byte-level view, so it can also be
 * an array element. */
int32_t last_value(_array struct reading *rs)
  _requires(rs._length == 3)
  _ensures(return == rs[2].value)
{
  return rs[2].value;
}

union record make_reading(int32_t value)
  _ensures(return.rd._active)
  _ensures(return.rd.value == value)
{
  union record r = { .rd = { .sensor = { 0 }, .value = value } };
  return r;
}

union record reading_roundtrip(int32_t value)
  _ensures(return.rd._active)
  _ensures(return.rd.value == value)
{
  union record r = make_reading(value);
  return r;
}
