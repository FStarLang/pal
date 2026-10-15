#include "pal.h"
#include <stdlib.h>

/* Giving a flexible-array-member object back.

   `vec_fam` covers allocating one and filling it; nothing covered freeing
   one, which is a different operation: a flexible struct has no whole-object
   storage view -- how big an object of the type is is not a fact about the
   type -- so it goes back the way it was handed over, in pieces, at the
   length the allocation asked for.

   This is C11 6.7.2.1p18 with the object's lifetime closed: the allocation
   names the tail's length, every store installs an effective type (6.5p6) on
   bytes that had none, and `free` takes back exactly what `malloc` gave. */
struct fam {
    size_t n;
    int a[];
};

void flex_free_roundtrip(void)
{
    size_t n = 4;
    struct fam *f = malloc(sizeof *f + n * sizeof(int));
    if (!f) return;

    f->n = n;
    f->a[0] = 7;

    free(f);
}
