#include "pal.h"

/* A contract can be written in a parameter's or result's type as well as in
   _requires/_ensures. Neither declaration below has a _requires or _ensures,
   but one says, with _plain, that the function neither takes nor returns
   ownership of the string. The annotated declaration is the contract whichever
   file PAL reads first.

     name_left:  annotated declaration here, bare declaration in b.c.
     name_right: bare declaration here, annotated declaration in b.c.

   Each caller lends a string it does not own, so it verifies only against the
   annotated contract. */

_plain const char *name_left(int status, _plain const char *fallback);

const char *name_right(int status, const char *fallback);

_plain const char *call_left(int status, _plain const char *fallback)
{
    return name_left(status, fallback);
}
