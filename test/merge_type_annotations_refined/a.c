#include "refined.h"

/* Each later declaration of a function is merged with the header's, in this
   file and in b.c, which also includes the header. The one stating more of
   the contract is kept, whichever is read first; what both state agrees.

     choose: the header annotates the types; this file adds a postcondition
       with the same annotations. Callers see the postcondition.
     keep: the header states the whole contract. The bare redeclaration below
       carries the header's annotated types, which clang copies onto every
       later declaration in the file, but not its _ensures. Callers still see
       the postcondition. */

_plain const char *choose(int status, _plain const char *fallback)
    _ensures(return == fallback);

const char *keep(int status, const char *fallback);

const char *choose(int status, const char *fallback)
{
    return fallback;
}

const char *keep(int status, const char *fallback)
{
    return fallback;
}
