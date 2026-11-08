#include "pal.h"
#include <stdint.h>

struct packet {
  int header;
  int payload;
};

struct message {
  _plain const struct packet *owner;
};

int read_without_handback(_plain struct message message)
  _ghost_arg(struct packet saved)
  _requires(_inline_pulse(
    Struct_packet.struct_packet_hole_header $(message.owner) 0.5R $(saved)))
  _ensures(_inline_pulse(
    Struct_packet.struct_packet_hole_header $(message.owner) 0.5R $(saved)))
{
  _assert(_inline_pulse(Struct_packet.struct_packet_hole_header
    $(message.owner) 0.5R $(saved)));
  _assert(_inline_pulse(Struct_packet.struct_packet_pts_to
    $(message.owner) 0.5R $(saved)));
  return message.owner->header;
}
