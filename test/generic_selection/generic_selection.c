#include "pal.h"
#include <stdint.h>

#define TYPE_WIDTH(value)                                                      \
  _Generic((value), uint32_t: 32u, uint64_t: 64u, default: 0u)

struct generic_slots {
  uint32_t narrow;
  uint64_t wide;
};

uint32_t select_uint32(uint32_t value) _ensures(return == value) {
  return _Generic((value), uint32_t: value, default: 0u);
}

void store_uint32(uint32_t *value) {
  _Generic((*value), uint32_t: *value, default: *value) = 42u;
}

uint32_t select_type_width_uint32(uint32_t value) _ensures(return == 32u) {
  return TYPE_WIDTH(value);
}

uint32_t select_type_width_uint64(uint64_t value) _ensures(return == 64u) {
  return TYPE_WIDTH(value);
}

uint64_t select_nested_uint64(uint64_t value) _ensures(return == value) {
  return _Generic((value),
      uint64_t: _Generic((value), uint64_t: value, default: 0ull),
      default: 0ull);
}

uint32_t ignore_unselected_side_effect(uint32_t value)
    _ensures(return == value) {
  return _Generic((value), uint32_t: value, default: value++);
}

void store_selected_narrow(struct generic_slots *slots, uint32_t selector)
    _ensures(slots->narrow == 42u) {
  _Generic((selector),
      uint32_t: slots->narrow,
      uint64_t: slots->wide,
      default: slots->narrow) = 42u;
}

void store_selected_wide(struct generic_slots *slots, uint64_t selector)
    _ensures(slots->wide == 84ull) {
  _Generic((selector),
      uint32_t: slots->narrow,
      uint64_t: slots->wide,
      default: slots->narrow) = 84ull;
}
