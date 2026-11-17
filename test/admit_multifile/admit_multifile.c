#include "pal.h"
#include <stdint.h>

/* Each marker below is missing from the other file's declaration. Like a
   contract, the markers must agree across translation units. */
_pal_admit int admitted_here(int x) _ensures(return == x);
int admitted_there(int x) _ensures(return == x);
_pal_ignore int ignored_here(int x);

int caller(void) _ensures(return == 2) {
    return admitted_here(1) + admitted_there(1);
}
