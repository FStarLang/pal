#include "pal.h"

/* Annotated types only: neither function takes or returns ownership of the
   string. a.c refines this declaration with a postcondition. */
_plain const char *choose(int status, _plain const char *fallback);

/* The whole contract. */
_plain const char *keep(int status, _plain const char *fallback)
    _ensures(return == fallback);
