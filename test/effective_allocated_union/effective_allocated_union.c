#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

union choice {
    int32_t *left _plain;
    int32_t *right _plain;
    float *incompatible _plain;
    uint64_t padding[3];
};

struct holder {
    int32_t tag;
    union choice payload;
};

void fresh_union(int32_t *p _plain) {
    union choice *u = malloc(sizeof(union choice));
    if (u == NULL) {
        return;
    }
    *u = (union choice) { .left = p };
    u->right = p;
    int32_t *q _plain = u->right;
    _assert(q == p);
    free(u);
}

void fresh_record(int32_t *p _plain) {
    struct holder *h = malloc(sizeof(struct holder));
    if (h == NULL) {
        return;
    }
    *h = (struct holder) {
        .tag = 0,
        .payload = (union choice) { .left = p },
    };
    h->payload.right = p;
    int32_t *q _plain = h->payload.right;
    _assert(q == p);
    free(h);
}
