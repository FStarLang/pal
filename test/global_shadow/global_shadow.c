#include "pal.h"

/*
 * A local or parameter shadows a file-scope global of the same name.
 *
 * check.rs resolved this correctly (check_var tries lookup_var before
 * lookup_global_var), but emit.rs asked lookup_global_var directly, so the two
 * passes disagreed about which variable an identifier denoted -- and emission
 * is the one that decides what F* sees.
 *
 * The consequences were bad in two different ways, both observed in FunOS's
 * cocovisor, where nucleus/mem_region_internal.h declares
 *
 *     extern struct mem_region regions[];
 *
 * and a static helper takes a parameter that happens to be named `regions`:
 *
 *   - For a MUTABLE global, emission refused to read the *parameter*,
 *     reporting "cannot read the mutable global ctr" and emitting `(admit())`
 *     in its place -- turning an ordinary read of an in-scope parameter into
 *     proof debt.
 *
 *   - For an ARRAY global (emitted as an empty module, being unsupported),
 *     emission qualified the parameter as `Global_regions.var_regions`, a
 *     dangling reference to a name that does not exist. Every consumer then
 *     failed with "Error 72: Identifier var_regions not found in module
 *     Global_regions", which reads like a proof failure and is nothing of the
 *     kind.
 *
 * Both spellings below must denote the parameter. The unshadowed case is here
 * too, because the obvious fix -- never consulting the globals -- would break
 * it, and it would break silently.
 */

const unsigned long limit = 42;

/* Unshadowed: `limit` is the global, so the result is pinned to its value.
   This is the regression guard in the other direction. */
unsigned long use_global(void)
	_ensures(return == 42)
{
	return limit;
}

/* Shadowed by a parameter. The postcondition is the discriminating one: it
   holds for every argument, so it is provable only if `limit` in the body
   denotes the parameter. Had it denoted the global, the body would return 42
   and this would fail for every argument but 42. */
unsigned long shadow_param(unsigned long limit)
	_ensures(return == limit)
{
	return limit;
}

/* Shadowed by a block-scope local, the other way C introduces a binding that
   hides a global. */
unsigned long shadow_local(unsigned long n)
	_ensures(return == n)
{
	unsigned long limit = n;
	return limit;
}
