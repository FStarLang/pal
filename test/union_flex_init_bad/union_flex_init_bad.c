#include "pal.h"
#include <stdint.h>

struct bitmap { uint64_t count; uint64_t words[]; };
union buffer { struct bitmap bitmap; uint8_t bytes[32]; };
struct context { int tag; union buffer buffer; };

void initialize(_out struct context *p)
{
    *p = (struct context){0};
    _assert(p->buffer.bitmap.words[2] == 0);
}
