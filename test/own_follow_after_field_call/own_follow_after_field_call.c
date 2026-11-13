#include "pal.h"
#include <stdint.h>

// A struct whose only owned member is `value`, and two members it does not own.
struct op {
    uint32_t status;
};

struct ctx {
    int *value;
    struct op op;
    uint32_t handle;
};

void op_init(_out struct op *op, uint32_t status)
    _ensures(op->status == status);

// The call initializes the unowned member through its address; the write after it then has to
// carry the struct's ownership across from the value the call left.
void init_then_write(struct ctx *c)
    _ensures(*c->value == _old(*c->value))
{
    op_init(&c->op, 0);
    c->handle = 0;
}
