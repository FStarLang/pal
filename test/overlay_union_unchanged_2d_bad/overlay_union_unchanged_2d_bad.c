#include "pal.h"
#include <stdint.h>

typedef struct _ROWS { uint8_t P[2][4]; } ROWS;
typedef struct _FLAT { uint8_t Q[8]; } FLAT;
typedef union _overlay _GRID { ROWS Rows; FLAT Flat; } GRID;

/* `P[1]` is bytes [4, 8), so a store to byte 5 changes it. */
void Grid_Scribble(GRID* g)
    _ensures(_unchanged(g->Rows.P[1]))
{
    g->Flat.Q[5] = 1;
}
