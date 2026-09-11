#include "pal.h"

/* Third occurrences for the declaration/definition arrangements in a.c.
   Parameter z differs from x in a.c and y in b.c. */

int triple_decl_specs_requires(int z)
{
    return z + 1;
}

int triple_decl_specs_ensures(int z)
{
    return z;
}

int triple_decl_specs_both(int z)
{
    return z + 1;
}

int triple_matching_decls_requires(int z)
    _requires(z > 0 && z < 100);
int triple_matching_decls_ensures(int z)
    _ensures(return == z);
int triple_matching_decls_both(int z)
    _requires(z > 0 && z < 100)
    _ensures(return == z + 1);

int triple_matching_defn_requires(int z)
    _requires(z > 0 && z < 100);
int triple_matching_defn_ensures(int z)
    _ensures(return == z);
int triple_matching_defn_both(int z)
    _requires(z > 0 && z < 100)
    _ensures(return == z + 1);

int triple_all_specs_requires(int z)
    _requires(z > 0 && z < 100)
{
    return z + 1;
}

int triple_all_specs_ensures(int z)
    _ensures(return == z)
{
    return z;
}

int triple_all_specs_both(int z)
    _requires(z > 0 && z < 100)
    _ensures(return == z + 1)
{
    return z + 1;
}
