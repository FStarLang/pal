#include "pal.h"
#include <stdint.h>

int duplicate(void) { return 1; }
int incompatible(int value);
const int repeated_object = 1;
struct collision { int first; };
typedef unsigned int collision_alias;
