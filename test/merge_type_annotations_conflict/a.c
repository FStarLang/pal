#include "pal.h"

/* Both declarations annotate the parameter's type, differently. Neither can be
   dropped in favour of the other. */
int pick(_plain const char *fallback);

/* One declaration annotates the parameter's type; the other, in b.c, also
   states a postcondition but annotates the parameter differently. The
   postcondition does not make the annotation it contradicts disappear. */
int length(_plain const char *s);
