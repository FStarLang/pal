#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef struct _G { uint8_t P[4]; uint32_t S; } G;
typedef struct _H { uint32_t A; uint32_t B; } H;
typedef union _overlay _U { G g; H h; } U;

/* `P[6]` is past the end of `P`, even though its byte is inside the union. */
void OutOfBounds(U* r)
    _ensures(_unchanged(r->g.P[6]))
{
    r->h.A = 1;
}

/* The offset of `P[i]` is not constant, so which bytes are meant is not
   known; equality of the views would be weaker than `_unchanged` promises. */
void Variable(U* r, size_t i)
    _requires(i < 4)
    _ensures(_unchanged(r->g.P[i]))
{
    r->h.B = 1;
}
