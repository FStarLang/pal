#include "pal.h"
#include <stdint.h>

typedef struct _ROWS { uint8_t P[2][4]; } ROWS;
typedef struct _FLAT { uint8_t Q[8]; } FLAT;
typedef union _overlay _GRID { ROWS Rows; FLAT Flat; } GRID;

/* `P[1][0]` is byte 4, so byte 1 is not what was written. */
void Grid_Set(GRID* g)
    _requires(g->Flat._active)
    _ensures(g->Flat.Q[1] == 7)
{
    g->Rows.P[1][0] = 7;
}
