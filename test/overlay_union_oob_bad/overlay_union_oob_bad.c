#include "pal.h"
#include <stdint.h>

typedef struct _G { uint8_t P[4]; uint32_t State; } G;
typedef struct _H { uint32_t A; uint32_t B; } H;
typedef union _overlay _U { G g; H h; } U;

/* `P[4]` is past the end of `P`, even though its byte is inside the union. */
void Oob(U* r)
    _ensures(r->h.B == 0u)
{
    r->g.P[4] = 0;
    r->g.P[5] = 0;
    r->g.P[6] = 0;
    r->g.P[7] = 0;
}
