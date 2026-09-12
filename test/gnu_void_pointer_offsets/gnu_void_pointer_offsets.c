#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* These postconditions check translation to raw byte-offset terms only.
 * No external calls, address laws, or storage-validity assumptions. */
void *minus_signed(void *base, int32_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset
      $(base) (-(FStar.Int32.v $(offset))))))
{
  return base - offset;
}

void *plus_signed(void *base, int32_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset
      $(base) (FStar.Int32.v $(offset)))))
{
  return base + offset;
}

void *negative_literal(void *base)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset $(base) (-4))))
{
  return base + (-4);
}

/* The minimum signed value must not be negated as a machine integer. */
void *minus_minimum(void *base)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset
      $(base) 2147483648)))
{
  return base - INT32_MIN;
}

void *unsigned_product(void *base, uint32_t slot, uint32_t slot_size)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset $(base)
      (FStar.UInt32.v (FStar.UInt32.mul_mod $(slot) $(slot_size))))))
{
  return base + slot * slot_size;
}

void *minus_unsigned(void *base, uint64_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset $(base)
      (-(FStar.UInt64.v $(offset))))))
{
  return base - offset;
}

void *unsigned_difference(void *base, uint32_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset $(base)
      (FStar.UInt32.v (FStar.UInt32.sub_mod $(offset) 1ul)))))
{
  return base + (offset - 1U);
}

void *bool_offset(void *base, _Bool offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset $(base)
      (if $(offset) then 1 else 0))))
{
  return base + offset;
}

typedef void byte;
typedef const volatile byte *raw_bytes;

raw_bytes qualified_alias(raw_bytes const base, int32_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset
      $(base) (FStar.Int32.v $(offset)))))
{
  raw_bytes result = base + offset;
  return result;
}

void *size_offset(void *base, size_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset
      $(base) (FStar.SizeT.v $(offset)))))
{
  return base + offset;
}

void *difference_offset(void *base, ptrdiff_t offset)
  _ensures(_inline_pulse(
    pure ($(return) == Pulse.Lib.C.GNU.VoidPointer.core_offset
      $(base) (-(Pulse.Lib.C.PtrdiffT.v $(offset))))))
{
  return base - offset;
}
