#include "pal.h"
#include <stdint.h>
#include "preprocessor_record.h"

/*
 * PAL writes down what clang's preprocessor gave its parser, in
 * preprocessor.json, so that a build can hold it to what its own compiler's
 * `-E` makes of the same source (see doc/internals.md). The expectation,
 * preprocessor-expect.json, pins what this file puts there: the header, the
 * `-D` from extra_opts, the macros the file tested and expanded, its pragmas,
 * and the tokens of a macro call that spans two lines.
 */

#ifdef PREPROCESSOR_RECORD_UNSET
#error "PREPROCESSOR_RECORD_UNSET is never defined"
#endif

#if PREPROCESSOR_RECORD_FLAG != 3
#error "extra_opts defines PREPROCESSOR_RECORD_FLAG to be 3"
#endif

/*
 * A pragma is not a token, so the record keeps its text. These two change
 * nothing. The second is a `_Pragma` that a macro expands to, and what is
 * recorded is the pragma, not the macro.
 */
#pragma push_macro("PREPROCESSOR_RECORD_TWICE")
#define PREPROCESSOR_RECORD_POP \
  _Pragma("pop_macro(\"PREPROCESSOR_RECORD_TWICE\")")
PREPROCESSOR_RECORD_POP

int32_t twice(int32_t x)
  _requires(x < 1000 && x > -1000)
  _ensures(return == x + x)
{
  return PREPROCESSOR_RECORD_TWICE(x);
}

/*
 * Compilers disagree about `__LINE__` in a macro call that spans lines: clang
 * gives the line the call ends on, GCC 12 the line it starts on. So the record
 * gives such a token both lines, and a build that compares PAL's tokens with
 * GCC's can tell this difference from any other.
 */
#define PREPROCESSOR_RECORD_LINE(x) __LINE__

int32_t line_of_call(void)
  _ensures(return == 51)
{
  return PREPROCESSOR_RECORD_LINE(
      0);
}
