#pragma once
#include "pal.h"

// These enumerators live in a header, so the pruner sees them as non-root
// declarations. The contract below is their only reference: the body uses a
// switch, whose case labels the C frontend folds to integer constants.
typedef enum _COLOR
{
    Color_Red = 0,
    Color_Green = 1,
    Color_Blue = 2,
} COLOR;

_Bool
color_is_known(COLOR c)
    _ensures(return == (c == Color_Red || c == Color_Green || c == Color_Blue));

COLOR
color_default(void)
    _ensures(return == Color_Green);
