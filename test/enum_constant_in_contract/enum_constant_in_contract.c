#include "pal.h"
#include <stdint.h>

// Clang inlines enumerators in C expressions. PAL parses contracts and
// executable _assert annotations itself; both must inline the same values
// without inventing storage for them.

typedef enum _COLOR
{
  Color_Red = 0,
  Color_Green = 1,
  Color_Blue = 2,
  Color_Max = 3,
} COLOR;

// The enumerator appears in both the precondition and the postcondition.
COLOR next_color(COLOR c)
  _requires(c < Color_Max)
  _ensures(return < Color_Max)
{
  _assert(c < Color_Max);
  COLOR result;

  if (c == Color_Blue)
  {
    result = Color_Red;
  }
  else
  {
    result = (COLOR)(c + 1);
  }

  return result;
}

// A validating accessor: the input is an untrusted byte, and the contract
// states exactly the invariant the body establishes on every path.
void classify(uint8_t raw, _out COLOR *out)
  _ensures(*out < Color_Max)
{
  if (raw >= Color_Max)
  {
    *out = Color_Red;
  }
  else
  {
    *out = (COLOR)raw;
  }

  _assert(*out < Color_Max);
}

enum { Limit_Negative = -3 };

void check_signed_enumerator(void)
{
  _assert(Limit_Negative == -3);
}
