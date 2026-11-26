#include "pal.h"

/* Both declarations annotate the parameter's type, differently. Neither can be
   dropped in favour of the other. */
int pick(_plain const char *fallback);
