#include "pal.h"
#include <stddef.h>
#include <stdint.h>
#include "tagged.h"

/*
 * Translating for a bare-metal target, through pal_opts:
 *
 *   --target=mips64-unknown-elf --clang-arg=-nostdlibinc
 *
 * A bare-metal target has no C library, and `-nostdlibinc` keeps the host's
 * headers out too, so every header here has to come from clang's resource
 * directory. PAL works that directory out from where libclang was loaded,
 * which for Debian's multiarch libclang gave /lib/lib/clang/20. That does not
 * exist, and `stddef.h` was not found. A Linux target hid this, because for
 * one clang also searches Debian's copy of its headers,
 * /usr/include/clang/20.1.8/include.
 */
#ifdef C2PULSE
#if !defined(__mips64) || defined(__linux__)
#error "--target did not reach clang"
#endif
#endif

/* An LP64 target: the sizes come from clang's layout for mips64. */
uint64_t lp64_sizes(void)
  _ensures(return == 16)
{
  return sizeof(size_t) + sizeof(uintptr_t);
}

/*
 * clang folds `offsetof` to a number before PAL sees it, so this function's
 * output is the literal 8, and `struct tagged` -- from a header, used nowhere
 * else -- is pruned from the output. Where the 8 came from is recorded only in
 * layout_table.json, which a build holds to its own compiler's layout, and
 * which layout-expect.json pins here.
 */
size_t tagged_value_offset(void)
  _ensures(return == 8)
{
  return offsetof(struct tagged, value);
}
