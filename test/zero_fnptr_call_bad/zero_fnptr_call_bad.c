#include "pal.h"
#include <stdint.h>
#include <string.h>

typedef int32_t (*callback)(int32_t);

struct handlers {
    uint32_t count;
    callback on_event;
};

int32_t neg(int32_t a)
    _requires(a > -100 && a < 100)
    _ensures(return == -a)
{
    return -a;
}

int32_t apply(callback op
                  _refine((_slprop) _inline_pulse(
                      is_valid $(this) true
                          (pre_of Funcptr_neg.func_neg__fp)
                          (post_of Funcptr_neg.func_neg__fp))),
              int32_t a)
    _requires(a > -100 && a < 100)
    _ensures(return == -a)
{
    return op(a);
}

// Control: a real function is callable through `apply`.
int32_t call_neg(int32_t x)
    _requires(x > -100 && x < 100)
    _ensures(return == -x)
{
    return apply(neg, x);
}

// A zeroed function pointer is null, and nothing says null is callable: the
// call cannot establish the callee's `is_valid`.
int32_t call_zeroed(struct handlers *h, int32_t x)
    _requires(x > -100 && x < 100)
{
    memset(h, 0, sizeof(*h));
    return apply(h->on_event, x);
}
