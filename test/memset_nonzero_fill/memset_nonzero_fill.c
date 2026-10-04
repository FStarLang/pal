/* Test: memset with a non-zero constant fill.
 *
 * C writes the fill byte (converted to unsigned char) into every byte. For a
 * whole fixed-size array whose element type is an integer, an enumeration or
 * a struct of those (unsigned bit-fields included), PAL builds the element
 * whose bytes are all that byte and fills every cell with it, so each field's
 * value afterwards is exactly what C leaves there. Debug builds use this to
 * "paint" a stack array before it is filled in.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <string.h>

typedef enum Kind { KIND_NONE = 0, KIND_ONE = 1 } Kind;

typedef struct Bits {
  uint8_t Flag : 1;
  uint8_t Rest : 7;
} Bits;

typedef struct Rec {
  uint64_t Wide;
  int32_t Signed;
  uint8_t Byte;
  Bits B;
  Kind K;
} Rec;

/* 0xFF: every integer field is all ones. */
uint64_t paint_wide(void)
  _ensures(return == 0xFFFFFFFFFFFFFFFFull)
{
  Rec a[3];
  memset(a, 0xFF, sizeof(a));
  return a[2].Wide;
}

/* A signed field holding all ones is -1. */
int32_t paint_signed(void)
  _ensures(return == -1)
{
  Rec a[3];
  memset(a, 0xFF, sizeof(a));
  return a[0].Signed;
}

/* An enumeration is its integer type: all ones need not be an enumerator. */
uint32_t paint_enum(void)
  _ensures(return == 0xFFFFFFFFu)
{
  Rec a[2];
  memset(a, 0xFF, sizeof(a));
  return (uint32_t)a[1].K;
}

/* 0xA5 = 1010'0101: each bit-field takes the bits at its own offset. */
uint32_t paint_bits(void)
  _ensures(return == 0x52)
{
  Rec a[2];
  memset(a, 0xA5, sizeof(a));
  uint32_t flag = a[0].B.Flag;
  uint32_t rest = a[0].B.Rest;
  return flag == 1 ? rest : 0;
}

/* The fill is converted to unsigned char, as C does: -1 writes 0xFF. */
uint8_t paint_minus_one(void)
  _ensures(return == 0xFF)
{
  Rec a[2];
  memset(a, -1, sizeof(a));
  return a[1].Byte;
}

/* Byte arrays take the fill byte in every cell, through either shape. */
void paint_bytes(uint8_t b[], size_t n)
  _requires(b._length == n && n > 0)
  _preserves_value(b._length)
  _ensures(b[0] == 0xAB)
{
  memset(b, 0xAB, n * sizeof(uint8_t));
}

uint8_t paint_local_bytes(void)
  _ensures(return == 0x5A)
{
  uint8_t b[8];
  memset(b, 0x5A, sizeof(b));
  return b[7];
}

/* A zero fill of a struct array is the same construction with byte 0. */
uint32_t zero_records(void)
  _ensures(return == 0)
{
  Rec a[2];
  memset(a, 0, sizeof(a));
  return (uint32_t)a[1].K + a[0].B.Rest;
}
