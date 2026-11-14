#include "pal.h"
#include <stddef.h>

// The node points at a gate that it need not own: the gate may be null, or
// shared with other nodes.
struct gate { int open; };
struct node { int x; struct gate *gate; };

// Nothing in the main file names this typedef, but it still makes
// `struct node` plain wherever the struct is used.
typedef _plain struct node PLAIN_NODE;
