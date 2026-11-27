#include "pal.h"
#include <stdint.h>

/* Asserting a user-defined loan is a proof obligation: with only half of
   the packet in hand, `Loan.struct_packet_hole_lent` at 1.0R is not there to
   assert, and the read through it is rejected. */

struct trailer {
  int counter;
};

struct packet {
  int header;
  unsigned char buffer[8];
  struct trailer trailer;
};

int peek_without_loan(_plain struct packet *p)
  _ghost_arg(struct packet saved)
  _preserves(_inline_pulse(Struct_packet.struct_packet_pts_to $(p) 0.5R $(saved)))
{
  _assert(_inline_pulse(Loan.struct_packet_hole_lent $(p) 1.0R $(saved)));
  return p->trailer.counter;
}
