/* Test: memset shapes PAL must reject.
 *
 * A non-zero fill is only modeled when PAL can build, at translation time,
 * the element value whose every byte is the fill byte. Anything else would
 * need a byte-level memory model, so PAL refuses rather than guess.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <string.h>

typedef struct WithPtr {
  uint32_t A;
  uint32_t *P;
} WithPtr;

typedef struct Plain {
  uint32_t A;
  uint32_t B;
} Plain;

/* The fill must be a translation-time constant. */
void fill_not_constant(uint8_t v)
{
  uint8_t b[4];
  memset(b, v, sizeof(b));
}

/* No pointer value has all bytes 0xFF. */
void fill_pointer_field(void)
{
  WithPtr a[2];
  memset(a, 0xFF, sizeof(a));
}

/* A _Bool byte holding 2 is not a value of the type. */
void fill_bool(void)
{
  bool a[4];
  memset(a, 2, sizeof(a));
}

/* Floating-point bit patterns are not modeled. */
void fill_float(void)
{
  float a[4];
  memset(a, 0xFF, sizeof(a));
}

/* A single object, not an array, with a non-zero fill. */
void fill_single_object(void)
{
  Plain s;
  memset(&s, 0xFF, sizeof(s));
}

/* Part of an array with a non-zero fill and a multi-byte element. */
void fill_partial(void)
{
  uint32_t a[4];
  memset(a, 0xFF, 2 * sizeof(uint32_t));
}
