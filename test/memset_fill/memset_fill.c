#include "pal.h"
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

struct record {
    bool valid;
    uint32_t count;
    uint8_t tag[4];
};

// A debug scribble over an object about to be written: the fill leaves no
// value of the struct (`valid` would hold 0xFF), so the object is held
// uninitialized before and after it.
void scribble(_plain struct record *r)
    _requires(_inline_pulse(struct_record_pts_to_uninit $(r)))
    _ensures(_inline_pulse(struct_record_pts_to_uninit $(r)))
{
    memset(r, 0xFF, sizeof(*r));
}

// A value held for the object is forgotten first.
void reset(_plain struct record *r)
    _requires(_inline_pulse(exists* v. struct_record_pts_to $(r) 1.0R v))
    _ensures(_inline_pulse(struct_record_pts_to_uninit $(r)))
{
    _ghost_stmt(struct_record_forget $(r));
    memset(r, 0xA5, sizeof(struct record));
}
