#include "pal.h"
#include <stdint.h>

/*
 * Translating for a target other than the host, through pal_opts:
 *
 *   --target=aarch64-unknown-linux-gnu
 *   --clang-arg=-ffreestanding --clang-arg=-DPAL_CLANG_ARG=1
 *
 * The C compiler that builds the test still builds for the host, so the checks
 * that the flags reached clang are made only under translation.
 */
#ifdef C2PULSE
#if !defined(__aarch64__)
#error "--target did not reach clang"
#endif
#if !defined(PAL_CLANG_ARG) || PAL_CLANG_ARG != 1
#error "--clang-arg did not reach clang"
#endif
#if __STDC_HOSTED__
#error "--clang-arg=-ffreestanding did not reach clang"
#endif
#endif

/*
 * Plain `char` is unsigned on AArch64 Linux and signed on x86-64, so this
 * contract holds only if the translation follows the target's ABI rather than
 * the host's.
 */
int32_t char_is_unsigned(void)
  _ensures(return == 200)
{
  char c = (char)200;
  return c;
}

/* An LP64 target: the sizes come from clang's layout for AArch64. */
uint64_t lp64_sizes(void)
  _ensures(return == 8)
{
  return sizeof(long) + sizeof(void *) - sizeof(int64_t);
}
