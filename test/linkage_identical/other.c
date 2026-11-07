#include "pal.h"
#include <stdint.h>

static const int32_t private_number = 7;
static int32_t private_value(void) _ensures(return == 7) {
    return private_number;
}

typedef uint32_t link_word;
link_word link_word_twice(link_word w) _requires(w <= 1000) _ensures(return == w + w) {
    return w + w;
}
