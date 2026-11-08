/*
 * Standalone case 22.1 (sink_p): evaluating a freed pointer's value.
 * C11 N1570 6.2.4p2 / Annex J.2:
 *   https://port70.net/~nsz/c/c11/n1570.html#6.2.4p2
 *
 * The pointer becomes indeterminate when its allocation's lifetime ends.
 * Passing it to a sink uses that value without dereferencing it.
 * This test intentionally exercises UB; observing its output proves nothing.
 */

#include "annotations.h"
#include <stdlib.h>
#include <stdint.h>

static volatile unsigned long long g_sink;

static void sink_p(_plain const void *v)
{
    g_sink ^= (unsigned long long)(uintptr_t)v;
}

static void case_22_1_use_a_freed_pointer_VALUE_sink_p(void)
{
    printf("\n== [UB] 22.1 (sink_p): passing a freed pointer to a sink ==\n");

    int *p = malloc(sizeof(int));
    if (!p) return;
    *p = 1;
    free(p);

    /* 6.2.4p2 / J.2: the argument evaluates p after the allocation's lifetime
       ends, independently of what sink_p does with that value. */
    sink_p(p);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    setvbuf(stdout, NULL, _IONBF, 0);
    case_22_1_use_a_freed_pointer_VALUE_sink_p();
    return 0;
}
