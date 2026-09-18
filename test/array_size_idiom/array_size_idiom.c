#include "pal.h"
#include <stdint.h>

/*
 * `ARRAY_SIZE(x)` -- `sizeof(x) / sizeof(*(x))` -- is the commonest way C
 * writes the capacity of a fixed-size array, and it is how a bounded walk
 * should be written: the bound comes from the array the compiler laid out, not
 * from a count parsed out of data.  (In the coco campaign, findings C6, C7 and
 * C8 are all the same defect -- a bound taken from parsed data, an access
 * strided by the compiler -- and the fix for each was to make ARRAY_SIZE the
 * bound and the parsed count merely a filter.)
 *
 * PAL translates it to
 *
 *     c_sizeof (full_array_lspec a n) / c_sizeof a
 *
 * `Pulse.Lib.C.Sizeof.c_sizeof_array` rewrites the numerator to
 * `c_sizeof a * n`, which leaves Z3 the NONLINEAR goal `(s * n) / s == n` with
 * `s` an uninterpreted positive.  This test exists because that is a shape one
 * would expect to be fragile, and because the idiom is load-bearing for a whole
 * class of real fixes.
 *
 * WHAT WAS MEASURED, and it is not what was expected.  A derived lemma
 * (`c_sizeof_array_div`, proved from `c_sizeof_array` and
 * `FStar.Math.Lemmas.multiple_division_lemma`, carrying an `SMTPat` on the
 * numerator) was written to discharge the division by rewriting instead of by
 * search.  It was then falsified in both directions and turned out to be
 * unnecessary:
 *
 *   - this test verifies with and without it;
 *   - so does coco's `cv_init_co3_exception_frames`, the largest real consumer
 *     of the idiom, even at `--z3rlimit_factor 1` (49s either way).
 *
 * So the lemma was NOT added.  An `SMTPat` is a global cost -- every query in
 * every PAL program pays for the trigger -- and there is no evidence it buys
 * anything.  It is recorded here rather than silently dropped so that the next
 * person to hit a slow `ARRAY_SIZE` goal knows the lemma exists, is a
 * three-line proof, and should be re-introduced only with a context where its
 * absence is demonstrably the cause.
 *
 * What this test IS, then, is a regression test for the idiom itself: if a
 * change to Pulse.Lib.C.Sizeof or to PAL's lowering of `sizeof` breaks
 * ARRAY_SIZE, this fails.
 */

#define ARRAY_SIZE(x) (sizeof(x) / sizeof(*(x)))

struct entry {
	uint32_t key;
	uint64_t val;
};

struct table {
	uint32_t claimed;	/* attacker-supplied occupancy */
	struct entry entries[8];
};

/* The bound is ARRAY_SIZE, the claimed count is only a filter. This is the
 * shape the coco fixes converged on, and it is the reason the guard must be an
 * ordinary C expression: `sizeof(<expression>)` is rejected inside an
 * annotation (coco/PAL_LIMITATIONS.md L43), so it cannot appear in an
 * `_invariant`. */
uint64_t lookup(struct table *t, uint32_t key)
{
	uint32_t i = 0;
	int found = 0;
	uint64_t out = 0;

	while (i < ARRAY_SIZE(t->entries) && !found)
		_invariant(_live(i))
		_invariant(_live(found))
		_invariant(_live(out))
	{
		if (i < t->claimed) {
			if (t->entries[i].key == key) {
				out = t->entries[i].val;
				found = 1;
			}
		}
		if (!found)
			i++;
	}
	return out;
}

/* ARRAY_SIZE as a value, on a local scalar array and on a char array. The
 * char case is the one where the division is against a size C actually fixes
 * (`c_sizeof_uint8_one`); the uint32_t case is the general one, where
 * `c_sizeof` is uninterpreted and only `c_sizeof_array` plus the division
 * lemma relate the two `sizeof`s. */
uint32_t sizes(void)
{
	uint32_t a[4] = {1, 2, 3, 4};
	char name[16] = {0};

	return (uint32_t)ARRAY_SIZE(a) + (uint32_t)ARRAY_SIZE(name);
}

/* ARRAY_SIZE of a fixed array reached through a pointer, which is the form
 * every use in coco takes. */
uint32_t capacity(struct table *t)
{
	return (uint32_t)ARRAY_SIZE(t->entries);
}
