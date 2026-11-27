#include "pal.h"
#include <stdint.h>

/* A user-defined loan: `Loan.struct_packet_hole_lent` is not generated, but
   its name ends in `struct_packet_hole_...`, so asserting it puts `*p` in
   pieces, like a generated hole. It omits `buffer` (lent elsewhere) and
   holds `trailer` at half. */

struct trailer {
  int counter;
};

struct packet {
  int header;
  unsigned char buffer[8];
  struct trailer trailer;
};

void stamp(_plain struct packet *p)
  _ghost_arg(struct packet saved)
  _requires(_inline_pulse(Loan.struct_packet_hole_lent $(p) 0.5R $(saved)))
  _ensures(_inline_pulse(Loan.struct_packet_hole_lent $(p) 0.5R
    { $(saved) with fld_header = $(saved.trailer.counter) }))
{
  _ghost_stmt(unfold (Loan.struct_packet_hole_lent $(p) 0.5R $(saved)));
  p->header = p->trailer.counter;
  _ghost_stmt(fold (Loan.struct_packet_hole_lent $(p) 0.5R
    { $(saved) with fld_header = $(saved.trailer.counter) }));
}

/* The loan asserted in the body, of a local: the contract holds the whole
   packet and lends `buffer` out itself, as a caller keeping a field on loan
   across calls would. */
int peek(_plain struct packet *p)
  _ghost_arg(struct packet saved)
  _preserves(_inline_pulse(Struct_packet.struct_packet_pts_to $(p) 1.0R $(saved)))
  _ensures(return == saved.trailer.counter)
{
  struct packet *local = p;
  int result;
  _ghost_stmt(Loan.lend_buffer $(local));
  _assert(_inline_pulse(Loan.struct_packet_hole_lent $(local) 1.0R $(saved)));
  _ghost_stmt(unfold (Loan.struct_packet_hole_lent $(local) 1.0R $(saved)));
  result = local->trailer.counter;
  _ghost_stmt(fold (Loan.struct_packet_hole_lent $(local) 1.0R $(saved)));
  _ghost_stmt(Loan.return_buffer $(local));
  _assert(_inline_pulse(Struct_packet.struct_packet_pts_to $(local) 1.0R $(saved)));
  return result;
}
