#include "pal.h"
#include <stdint.h>

static const int32_t private_number = 7;
static int32_t private_value(void) _ensures(return == 7) {
    return private_number;
}

/* glibc's <stdio.h> and clang's <stdarg.h> name `va_list` through different
   typedef chains; the definitions agree because the types do. */
typedef uint32_t link_word_base;
typedef link_word_base link_word;
link_word link_word_echo(link_word w) _ensures(return == w) { return w; }
