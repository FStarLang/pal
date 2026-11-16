#include "pal.h"
#include <stdint.h>

struct inner { uint32_t x; };
struct outer { struct inner in; uint32_t n; };

uint32_t read_inner(const struct inner *p)
    _ensures(return == p->x);

/* Taking the parameter's address in ghost code makes it a slot. The
   explicit focus is the author's, not a second focus for field_args. */
uint32_t manually_focused(const struct outer *p)
    _ensures(return == p->in.x)
{
    _ghost_stmt(
        with saved. assert ptr_pts_to $&(p) 1.0R saved;
        Struct_outer.struct_outer_focus_in saved);
    uint32_t x = read_inner(&p->in);
    _ghost_stmt(Struct_outer.struct_outer_unfocus_read_in saved);
    return x;
}

struct owner { struct outer *p; };

/* A deep pointer field still needs the automatic lending added for
   MountStore, even though its address cannot be grouped statically. */
uint32_t automatically_focused(struct owner *o)
    _ensures(return == o->p->in.x)
{
    return read_inner(&o->p->in);
}
