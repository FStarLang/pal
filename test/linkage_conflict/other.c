#include "pal.h"
int duplicate(void) { return 2; }
int incompatible(unsigned value) { return value; }
const int repeated_object = 2;
struct collision { int second; };
typedef unsigned long long collision_alias;
