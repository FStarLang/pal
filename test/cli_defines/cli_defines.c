#include "pal.h"
#include <stdint.h>

/*
 * Command-line preprocessor flags, supplied through extra_opts.
 *
 * -D: the define must reach the preprocessor, or the #error fires and
 * translation fails.
 */
#if !defined(PAL_TEST_FLAG) || PAL_TEST_FLAG != 7
#error "-D did not reach the preprocessor"
#endif

/*
 * -I precedence: first/shadow.h and second/shadow.h both exist, and C gives
 * the first -I on the command line precedence. The contract below pins the
 * value from first/.
 */
#include <shadow.h>

int32_t which_shadow(void)
  _ensures(return == 1)
{
  return SHADOW_WHICH;
}

/*
 * Builtins with no program meaning: __builtin_expect(e, c) is e, and
 * __builtin_constant_p(e) folds to 0, which selects the general path.
 */
int32_t expect_is_identity(int32_t x)
  _ensures(return == x)
{
  if (__builtin_expect(x == 0, 0))
    return 0;
  return x;
}

int32_t constant_p_is_false(int32_t x)
  _ensures(return == x)
{
  if (__builtin_constant_p(x))
    return 0;
  return x;
}
