#include "pal.h"
#include <stdlib.h>

typedef int *int_ptr _allocated;

int_ptr alloc_int() {
    int *p = (int *) malloc(sizeof(int));
    *p = 0;
    return p;
}

int alloc_and_free(int x) {
    free(alloc_int());
    return 42;
}
