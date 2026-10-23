#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

union choice {
    int32_t *integer _plain;
    float *floating _plain;
};

void incompatible_switch(int32_t *p _plain, float *q _plain) {
    union choice *u = malloc(sizeof(union choice));
    if (u == NULL) {
        return;
    }
    *u = (union choice) { .integer = p };
    u->floating = q;
    free(u);
}
