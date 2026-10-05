#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

struct item { uint32_t kind; uint32_t len; uint32_t flag; };

// `p != NULL && A && B` parses as `(p != NULL && A) && B`; B must still see
// the pointer as non-null.
uint32_t chain3(_nullable struct item *p)
{
    uint32_t r = 0;
    if (p != NULL && p->kind == 2 && p->len > 0)
    {
        r = p->flag;
    }
    return r;
}

// The then-branch of a two-way chain reads through the pointer.
uint32_t chain2_body(_nullable struct item *p)
{
    uint32_t r = 0;
    if (p != NULL && p->kind == 2)
    {
        r = p->len;
    }
    return r;
}

// The then-branch writes through the pointer.
void chain2_write(_nullable struct item *p)
{
    if (p != NULL && p->kind == 2 && p->len > 0)
    {
        p->flag = 1;
    }
}

// Four conjuncts, used as a value rather than as a branch condition.
bool chain4_value(_nullable struct item *p)
{
    bool b = p != NULL && p->kind == 2 && p->len > 0 && p->flag != 0;
    return b;
}

// The then-branch returns early.
uint32_t chain3_return(_nullable struct item *p)
{
    if (p != NULL && p->kind == 2 && p->len > 0)
    {
        return p->flag;
    }
    return 0;
}
