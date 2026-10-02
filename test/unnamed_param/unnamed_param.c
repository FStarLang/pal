#include <stddef.h>
#include "pal.h"

/* A prototype may leave its parameters unnamed. The synthesized name must be
 * registered in the environment, or the generated spec dereferences a
 * by-value parameter and the module is ill-typed. */

typedef unsigned char cluster_t;

/* Unnamed parameter of typedef type: the case that regressed. */
size_t unnamed_typedef(cluster_t);

/* The same declaration, named -- the two must agree. */
size_t named_typedef(cluster_t c);

/* Unnamed parameter of builtin type. */
size_t unnamed_builtin(unsigned char);

/* Several unnamed parameters, to pin the index used for each name. */
size_t unnamed_several(cluster_t, unsigned int, cluster_t);

/* Mixed named and unnamed. */
size_t unnamed_mixed(cluster_t a, cluster_t, unsigned int c);

/* A definition whose prototype above is unnamed: merge must not confuse the
 * synthesized declaration name with the definition's real one. */
size_t defined_later(cluster_t);

size_t defined_later(cluster_t cl)
{
	return (size_t)cl;
}
