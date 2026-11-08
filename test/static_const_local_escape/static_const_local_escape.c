#include "pal.h"
#include <stdint.h>

/* A block-scope `static const` is translated as a local initialized on each
   call, so one whose address is taken -- and could escape the call -- is
   rejected, as is a block-scope static that is not itself const. */

const uint32_t *escaping_array(void) {
    static const uint32_t table[] = {10, 20, 30};
    return table;
}

const uint32_t *escaping_element(void) {
    static const uint32_t table[] = {10, 20, 30};
    return &table[1];
}

const uint32_t *escaping_scalar(void) {
    static const uint32_t answer = 42;
    return &answer;
}

/* A pointer to const is itself mutable static storage. */
const uint32_t *pointer_to_const(void) {
    static const uint32_t *p = 0;
    return p;
}
