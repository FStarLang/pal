#include "pal.h"
struct flags { _Bool value : 1; };

struct flags clear(void)
    _ensures(_inline_pulse(pure (($(return)).Struct_flags.fld_bits0 == 0uy)))
{
    return (struct flags){ .value = 0 };
}
