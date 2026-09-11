#include "pal.h"

/* Counterparts of the declarations in a.c and c.c. Different parameter names
   exercise contract comparison and transfer up to parameter renaming. */

int decl_defn_same_requires(int y)
    _requires(y > 0 && y < 100)
{
    return y + 1;
}

int decl_defn_same_ensures(int y)
    _ensures(return == y)
{
    return y;
}

int decl_defn_same_both(int y)
    _requires(y > 0 && y < 100)
    _ensures(return == y + 1)
{
    return y + 1;
}

int decl_defn_decl_only_requires(int y)
{
    return y + 1;
}

int decl_defn_decl_only_ensures(int y)
{
    return y;
}

int decl_defn_decl_only_both(int y)
{
    return y + 1;
}

int decl_decl_left_requires(int y);
int decl_decl_left_ensures(int y);
int decl_decl_left_both(int y);

int decl_decl_right_requires(int y)
    _requires(y > 0 && y < 100);
int decl_decl_right_ensures(int y)
    _ensures(return == y);
int decl_decl_right_both(int y)
    _requires(y > 0 && y < 100)
    _ensures(return == y + 1);

int decl_decl_same_requires(int y)
    _requires(y > 0 && y < 100);
int decl_decl_same_ensures(int y)
    _ensures(return == y);
int decl_decl_same_both(int y)
    _requires(y > 0 && y < 100)
    _ensures(return == y + 1);

int triple_decl_specs_requires(int y);
int triple_decl_specs_ensures(int y);
int triple_decl_specs_both(int y);

int triple_matching_decls_requires(int y)
{
    return y + 1;
}

int triple_matching_decls_ensures(int y)
{
    return y;
}

int triple_matching_decls_both(int y)
{
    return y + 1;
}

int triple_matching_defn_requires(int y);
int triple_matching_defn_ensures(int y);
int triple_matching_defn_both(int y);

int triple_all_specs_requires(int y)
    _requires(y > 0 && y < 100);
int triple_all_specs_ensures(int y)
    _ensures(return == y);
int triple_all_specs_both(int y)
    _requires(y > 0 && y < 100)
    _ensures(return == y + 1);
