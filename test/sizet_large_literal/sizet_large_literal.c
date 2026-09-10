#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/*
 * F* writes size_t literals as `Nsz`, and that notation is only valid for
 * N <= 65535 -- `fits_at_least_16` is the only bound available without a
 * platform assumption. PAL emitted `65536sz` for anything larger, which F*
 * rejects outright with "65536 is not in the expected range for FStar.SizeT",
 * so a struct containing a buffer of 64KiB or more could not be translated at
 * all.
 *
 * Pulse.Lib.C.Assumptions already assumes `fits_u64` with an SMTPat, so the
 * larger values are provable -- they just need to be written as a conversion
 * rather than as a literal.
 *
 * Sizes chosen around the boundary: below, exactly at, and well above.
 */

struct small_buf {
	uint8_t data[65535];
};

struct boundary_buf {
	uint8_t data[65536];
};

struct large_buf {
	uint8_t data[1048576];
};

size_t small_size(void)  { return sizeof(struct small_buf); }
size_t boundary_size(void) { return sizeof(struct boundary_buf); }
size_t large_size(void)  { return sizeof(struct large_buf); }

size_t big_literal(void) { return (size_t)1048576; }
