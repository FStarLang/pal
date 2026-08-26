#include "pal.h"
#include <stdint.h>

// Enumerators are inlined by Clang as integer literals wherever they appear in
// a function *body*. Contracts are different: they are raw source snippets that
// PAL parses itself, so Clang never sees those uses and an enumerator there
// used to be an unresolved name ("unknown local variable Color_Max").
//
// PAL now publishes each enumerator as a pure global constant, so a contract
// can name it instead of repeating its value. Unreferenced globals are pruned,
// so this costs nothing when an enumerator is only used from a body.
//
// "Constant" is meant in C's sense: an enumerator names a value and has no
// storage, so `&Color_Red` is not something that can be written. Each one is
// emitted as a bare `let`, without the address, non-null axiom and acquire that
// a real global carries -- assuming a cell for it would assume storage that
// nothing can ever produce.

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
}
