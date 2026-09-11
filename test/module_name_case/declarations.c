#include "pal.h"
#include <stdbool.h>

typedef int number;
typedef int Number;

union item { int value; };
union Item { int value; };

struct parcel { int *p; };
struct Parcel { int *p; };

int read_lower(struct parcel *x) _ensures(return == *x->p)
{
    return *x->p;
}

int read_upper(struct Parcel *x) _ensures(return == *x->p)
{
    return *x->p;
}

int use_types(void) _ensures(return == 9)
{
    number a = 4;
    Number b = 5;
    union item x = { .value = a };
    union Item y = { .value = b };
    return x.value + y.value;
}

const int count = 5;
const int Count = 6;

int use_globals(void) _ensures(return == 11)
{
    return count + Count;
}

int mutable;
int Mutable;

bool use_addresses(void) _ensures(return == true)
{
    int *p = &mutable;
    int *q = &Mutable;
    return p == &mutable && q == &Mutable;
}

_type(values, list Int32.t)
_type(Values, list Int32.t)

_let(values empty_lower(), _inline_pulse([]))
_let(Values empty_upper(), _inline_pulse([]))

_let(_specint amount(), 1)
_let(_specint Amount(), 2)

void use_lets(void)
{
    _assert(amount() == 1);
    _assert(Amount() == 2);
}

_include_pulse(Case_types,
    let lower : $type(values) = []
    let upper : $type(Values) = []
)

_include_pulse(Func_reserved,
    let marker = 17
)

int reserved(void) _ensures(return == 17) { return 17; }
int use_reserved(void) _ensures(return == 17) { return reserved(); }
