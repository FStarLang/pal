#include "pal.h"
#include <stdint.h>

typedef long double omitted_float _pal_ignore;
typedef struct _pal_ignore {
    int signed_bits : 3;
    long double value;
} omitted_record _pal_ignore;

struct _pal_ignore omitted_struct {
    int signed_bits : 3;
    struct nested_omitted { long double value; } nested;
};

union _pal_ignore omitted_union {
    int signed_bits : 3;
    long double value;
};

enum _pal_ignore omitted_enum { omitted_constant = 7 };

_pal_ignore long double omitted_global = 1.0L;

struct kept_struct {
    int value;
};

int kept(int x) _ensures(return == x) {
    typedef long double local_float _pal_ignore;
    struct _pal_ignore local_record { int signed_bits : 3; };
    _pal_ignore long double local_value = ({
        __asm__ volatile ("");
        1.0L;
    });
    return x;
}
