#include "pal.h"
#include <stdbool.h>
#include <stddef.h>

/* The right operand of && and || reads an array cell that is only in
 * bounds when the left operand short-circuits as C says it does. */
/* A guard such as `i <= len && a[i] == 0` is intentionally not accepted:
 * the left operand does not prove the index bound when i == len. It was
 * checked by hand and fails verification with the expected array bound VC. */

void observe(bool b)
  _ensures(true)
{
}

typedef struct FlagBox {
  bool ok;
} FlagBox;

typedef struct OptionalBox {
  int x;
} OptionalBox;

size_t find_first_and(_array int *a, size_t len)
  _requires(a._length == len)
  _preserves_value(a._length)
  _ensures(return <= len)
{
  size_t i = 0;
  while (i < len && a[i] == 0)
    _invariant(_live(i))
    _invariant(i <= len)
  {
    i++;
  }
  return i;
}

size_t find_first_or(_array int *a, size_t len)
  _requires(a._length == len)
  _preserves_value(a._length)
  _ensures(return <= len)
{
  size_t i = 0;
  while (!(i >= len || a[i] != 0))
    _invariant(_live(i))
    _invariant(i <= len)
  {
    i++;
  }
  return i;
}

bool cell_is_zero(_array int *a, size_t len, size_t i)
  _requires(a._length == len)
  _preserves_value(a._length)
{
  if (i < len && a[i] == 0)
    return true;
  bool r = i < len && a[i] == 0;
  r = i < len && a[i] == 0;
  observe(i < len && a[i] == 0);
  return r || (i < len && a[i] == 1);
}

bool write_short_circuit_forms(_array int *a, size_t len, size_t i, bool choose)
  _requires(a._length == len)
  _preserves_value(a._length)
{
  bool tmp = false;
  bool* out = &tmp;
  FlagBox box = {0};
  box.ok = i < len && a[i] == 0;
  *out = i < len && a[i] == 1;
  bool r = choose ? (i < len && a[i] == 0) : (i < len && a[i] == 1);
  switch ((i < len && a[i] == 2) ? 1 : 0) {
  case 1:
    observe(true);
    break;
  default:
    observe(false);
    break;
  }
  r = box.ok || *out;
  return r;
}

bool nullable_member_guard(_nullable const OptionalBox *p)
{
  if (p != NULL && p->x == 0)
    return true;
  return false;
}
