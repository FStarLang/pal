#include "pal.h"
#include <stdint.h>

/* Arrays whose elements are union-containing records (moved here from
 * union_struct_arms). The effective-type model requires a union-containing
 * object to have a declared (fixed) destination before it can be claimed or
 * read, but array elements only carry the non-nominal per-element view
 * (`object_read_ok`, see model_memberwise_element_is_not_nominal in
 * Pulse.Lib.C.Palow.Array), so the generated element fill/read helpers cannot
 * establish `ET.declared_destination` / `ET.read_ok` for each element.
 * Expected to fail verification until the array model can carry nominal
 * element facts. */

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

struct envelope {
  uint32_t sequence;
  union record record;
};

struct envelope_pair {
  struct envelope values[2];
};

struct envelope_pair make_envelope_pair(int32_t first, int32_t second)
  _ensures(return.values[0].record.rd._active && return.values[1].record.rd._active)
  _ensures(return.values[0].record.rd.value == first)
  _ensures(return.values[1].record.rd.value == second)
{
  struct envelope_pair result = {
    .values = {
      { .sequence = 0, .record = { .rd = { .sensor = { 0 }, .value = 0 } } },
      { .sequence = 0, .record = { .rd = { .sensor = { 0 }, .value = 0 } } }
    }
  };
  result.values[0].record.rd.value = first;
  result.values[1].record.rd.value = second;
  return result;
}

struct envelope_pair partially_initialized_pair(uint32_t sequence)
  _ensures(return.values[0].record.rd._active && return.values[1].record.rd._active)
  _ensures(return.values[0].sequence == sequence && return.values[1].sequence == 0)
  _ensures(return.values[0].record.rd.value == 0)
  _ensures(return.values[1].record.rd.sensor[3] == 0)
{
  struct envelope_pair result = { .values = { { .sequence = sequence } } };
  return result;
}
