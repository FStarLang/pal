#include "pal.h"
#include <stdint.h>

struct packet {
  int header;
  unsigned char buffer[8];
};

int read_detached(_plain const struct packet *p)
  _ghost_arg(struct packet saved)
  _requires(_inline_pulse(
    Struct_packet.struct_packet_hole_header $(p) 1.0R $(saved)))
  _ensures(_inline_pulse(
    Struct_packet.struct_packet_hole_header $(p) 1.0R $(saved)))
{
  _ghost_stmt(unfold (Struct_packet.struct_packet_hole_header
    $(p) 1.0R $(saved)));
  int result = p->header;
  _ghost_stmt(fold (Struct_packet.struct_packet_hole_header
    $(p) 1.0R $(saved)));
  return result;
}
