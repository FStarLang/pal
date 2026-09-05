#include "pal.h"

/* The standard C idiom for a self-referential type: the pointer typedef is
   declared before the struct it points to, and is then used as the field type
   inside that very struct. */

typedef struct node_t *nodeptr;

typedef struct node_t {
    int tag;
    nodeptr next;
} node_t;

int head_tag(nodeptr p)
{
    return p->tag;
}

/* The same idiom with the typedef reached through another typedef. */

typedef struct link_t *linkptr;
typedef linkptr linkptr_alias;

typedef struct link_t {
    int tag;
    linkptr_alias next;
} link_t;

int link_tag(linkptr p)
{
    return p->tag;
}
