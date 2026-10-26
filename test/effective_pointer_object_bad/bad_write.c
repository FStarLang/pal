#include "pal.h"

/* Check writes independently so rejecting the read cannot mask this case. */
void bad_write(int **p, float *value _plain) {
    *(float **)p = value;
}
