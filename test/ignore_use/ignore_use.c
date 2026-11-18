#include "pal.h"
#include <stdint.h>

_pal_ignore int ignored_fn(int x);
struct _pal_ignore ignored_rec { int a; };
typedef int ignored_int _pal_ignore;
_pal_ignore int ignored_global;

int call_ignored(void) { return ignored_fn(1); }

int (*ref_ignored(void))(int) { return ignored_fn; }

int field_of_ignored(struct ignored_rec *r) _requires(r != 0) { return r->a; }

int typedef_param(ignored_int x) { return 0; }

int read_ignored_global(void) { return ignored_global; }

int read_ignored_local(void) {
    _pal_ignore int y = 3;
    return y;
}
