#include "pal.h"

/* The shared ptr_ctype must not authorize incompatible pointer-object reads. */
float *bad_read(int **p) {
    return *(float **)p;
}
