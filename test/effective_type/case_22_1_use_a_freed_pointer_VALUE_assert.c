/*
 * Standalone case 22.1 (assert): evaluating a freed pointer's value.
 * C11 N1570 6.2.4p2 / Annex J.2:
 *   https://port70.net/~nsz/c/c11/n1570.html#6.2.4p2
 *
 * The pointer becomes indeterminate when its allocation's lifetime ends.
 * Comparing it with NULL is problematic even without dereferencing it.
 * This intentionally exercises UB when assertions are enabled; do not define
 * NDEBUG when running this test.
 */

#include <assert.h>
#include "annotations.h"
#include <stdlib.h>
#include <stddef.h>

static void case_22_1_use_a_freed_pointer_VALUE_assert(void)
{
    printf("\n== [UB] 22.1 (assert): comparing a freed pointer with NULL ==\n");

    int *p = malloc(sizeof(int));
    if (!p) return;
    *p = 1;
    free(p);

    /* 6.2.4p2 / J.2: evaluating p in this comparison uses its indeterminate
       value, not the value of the object it used to point to. */
    assert(p != NULL);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    setvbuf(stdout, NULL, _IONBF, 0);
    case_22_1_use_a_freed_pointer_VALUE_assert();
    return 0;
}
