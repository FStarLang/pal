#include "pal.h"

/* Cross-file counterparts of merge_specs.c. Each arrangement covers requires
   only, ensures only, and both. The tested declarations are NOT in a shared
   header, so Clang cannot inherit their attributes across files.

   All enabled examples are intended to verify:
     decl_defn_same: matching contracts on declaration and definition.
     decl_defn_decl_only: contracted declaration, bare definition.
     decl_decl_left: contracted declaration here, bare declaration in b.c.
     decl_decl_right: bare declaration here, contracted declaration in b.c.
     decl_decl_same: matching contracted declarations, no definition.

   Three-file arrangements (each also covers all three contract kinds):
     triple_decl_specs: contracted decl here, bare decl in b.c, bare defn in c.c.
     triple_matching_decls: matching decls here and in c.c, bare defn in b.c.
     triple_matching_defn: contracted defn here, bare decl in b.c, matching decl in c.c.
     triple_all_specs: matching contracted decls here and in b.c, matching defn in c.c.

   As in merge_specs.c, intentional conflicts are not enabled:
     conflicting decl/defn specs => "differing specifications";
     specs on the definition only => "specifications should be on the declaration";
     conflicting decl/decl specs => "differing specifications".

   Verify all six orders of a.c, b.c, and c.c. Callers check retained postconditions.
   Valid calls alone cannot detect a dropped precondition, so also inspect the
   generated requires clauses. Definitions use x + 1 where the precondition
   must establish arithmetic safety; ensures-only definitions use identity. */

int decl_defn_same_requires(int x)
    _requires(x > 0 && x < 100);
int decl_defn_same_ensures(int x)
    _ensures(return == x);
int decl_defn_same_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int decl_defn_decl_only_requires(int x)
    _requires(x > 0 && x < 100);
int decl_defn_decl_only_ensures(int x)
    _ensures(return == x);
int decl_defn_decl_only_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int decl_decl_left_requires(int x)
    _requires(x > 0 && x < 100);
int decl_decl_left_ensures(int x)
    _ensures(return == x);
int decl_decl_left_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int decl_decl_right_requires(int x);
int decl_decl_right_ensures(int x);
int decl_decl_right_both(int x);

int decl_decl_same_requires(int x)
    _requires(x > 0 && x < 100);
int decl_decl_same_ensures(int x)
    _ensures(return == x);
int decl_decl_same_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int triple_decl_specs_requires(int x)
    _requires(x > 0 && x < 100);
int triple_decl_specs_ensures(int x)
    _ensures(return == x);
int triple_decl_specs_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int triple_matching_decls_requires(int x)
    _requires(x > 0 && x < 100);
int triple_matching_decls_ensures(int x)
    _ensures(return == x);
int triple_matching_decls_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int triple_matching_defn_requires(int x)
    _requires(x > 0 && x < 100)
{
    return x + 1;
}

int triple_matching_defn_ensures(int x)
    _ensures(return == x)
{
    return x;
}

int triple_matching_defn_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1)
{
    return x + 1;
}

int triple_all_specs_requires(int x)
    _requires(x > 0 && x < 100);
int triple_all_specs_ensures(int x)
    _ensures(return == x);
int triple_all_specs_both(int x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + 1);

int call_decl_defn_same_requires(void)
{
    return decl_defn_same_requires(5);
}

int call_decl_defn_same_ensures(void) _ensures(return == 5)
{
    return decl_defn_same_ensures(5);
}

int call_decl_defn_same_both(void) _ensures(return == 6)
{
    return decl_defn_same_both(5);
}

int call_decl_defn_decl_only_requires(void)
{
    return decl_defn_decl_only_requires(5);
}

int call_decl_defn_decl_only_ensures(void) _ensures(return == 5)
{
    return decl_defn_decl_only_ensures(5);
}

int call_decl_defn_decl_only_both(void) _ensures(return == 6)
{
    return decl_defn_decl_only_both(5);
}

int call_decl_decl_left_requires(void)
{
    return decl_decl_left_requires(5);
}

int call_decl_decl_left_ensures(void) _ensures(return == 5)
{
    return decl_decl_left_ensures(5);
}

int call_decl_decl_left_both(void) _ensures(return == 6)
{
    return decl_decl_left_both(5);
}

int call_decl_decl_right_requires(void)
{
    return decl_decl_right_requires(5);
}

int call_decl_decl_right_ensures(void) _ensures(return == 5)
{
    return decl_decl_right_ensures(5);
}

int call_decl_decl_right_both(void) _ensures(return == 6)
{
    return decl_decl_right_both(5);
}

int call_decl_decl_same_requires(void)
{
    return decl_decl_same_requires(5);
}

int call_decl_decl_same_ensures(void) _ensures(return == 5)
{
    return decl_decl_same_ensures(5);
}

int call_decl_decl_same_both(void) _ensures(return == 6)
{
    return decl_decl_same_both(5);
}

int call_triple_decl_specs_requires(void)
{
    return triple_decl_specs_requires(5);
}

int call_triple_decl_specs_ensures(void) _ensures(return == 5)
{
    return triple_decl_specs_ensures(5);
}

int call_triple_decl_specs_both(void) _ensures(return == 6)
{
    return triple_decl_specs_both(5);
}

int call_triple_matching_decls_requires(void)
{
    return triple_matching_decls_requires(5);
}

int call_triple_matching_decls_ensures(void) _ensures(return == 5)
{
    return triple_matching_decls_ensures(5);
}

int call_triple_matching_decls_both(void) _ensures(return == 6)
{
    return triple_matching_decls_both(5);
}

int call_triple_matching_defn_requires(void)
{
    return triple_matching_defn_requires(5);
}

int call_triple_matching_defn_ensures(void) _ensures(return == 5)
{
    return triple_matching_defn_ensures(5);
}

int call_triple_matching_defn_both(void) _ensures(return == 6)
{
    return triple_matching_defn_both(5);
}

int call_triple_all_specs_requires(void)
{
    return triple_all_specs_requires(5);
}

int call_triple_all_specs_ensures(void) _ensures(return == 5)
{
    return triple_all_specs_ensures(5);
}

int call_triple_all_specs_both(void) _ensures(return == 6)
{
    return triple_all_specs_both(5);
}
