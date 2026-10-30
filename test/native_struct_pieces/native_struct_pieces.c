#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

struct trailer {
  int counter;
};

struct packet {
  int header;
  unsigned char buffer[8];
  struct trailer trailer;
};

struct envelope {
  int tag;
  struct packet core;
};

int read_nested_offset(_plain const struct envelope *p)
  _ghost_arg(int x)
  _requires(_inline_pulse(int32_t_pts_to
    (($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_header) 0.5R $(x)))
  _ensures(_inline_pulse(int32_t_pts_to
    (($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_header) 0.5R $(x)))
  _ensures(return == x)
{
  return p->core.header;
}

void write_nested_offset(_plain struct envelope *p, int x)
  _ghost_arg(int before)
  _requires(_inline_pulse(int32_t_pts_to
    (($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_header) 1.0R $(before)))
  _ensures(_inline_pulse(int32_t_pts_to
    (($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_header) 1.0R $(x)))
{
  p->core.header = x;
}

int read_hole(_plain const struct packet *p)
  _ghost_arg(struct packet saved)
  _requires(_inline_pulse(
    Struct_packet.struct_packet_hole_buffer $(p) 0.5R $(saved)))
  _ensures(_inline_pulse(
    Struct_packet.struct_packet_hole_buffer $(p) 0.5R $(saved)))
  _ensures(return == saved.header)
{
  _ghost_stmt(unfold (Struct_packet.struct_packet_hole_buffer
    $(p) 0.5R $(saved)));
  int result = p->header;
  _ghost_stmt(fold (Struct_packet.struct_packet_hole_buffer
    $(p) 0.5R $(saved)));
  return result;
}

int read_nested_holes(_plain const struct envelope *p)
  _ghost_arg(struct envelope saved)
  _requires(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(p) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(p) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(return == saved.core.trailer.counter)
{
  _ghost_stmt(unfold (Struct_envelope.struct_envelope_hole_core
    $(p) 0.5R $(saved)));
  _ghost_stmt(unfold (Struct_packet.struct_packet_hole_buffer
    ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
    0.5R $(saved.core)));
  int result = p->core.trailer.counter;
  _ghost_stmt(fold (Struct_packet.struct_packet_hole_buffer
    ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
    0.5R $(saved.core)));
  _ghost_stmt(fold (Struct_envelope.struct_envelope_hole_core
    $(p) 0.5R $(saved)));
  return result;
}

void write_hole(_plain struct packet *p, int x)
  _ghost_arg(struct packet saved)
  _requires(_inline_pulse(
    Struct_packet.struct_packet_hole_buffer $(p) 1.0R $(saved)))
  _ensures(_inline_pulse(
    Struct_packet.struct_packet_hole_buffer
      $(p) 1.0R { $(saved) with fld_header = $(x) }))
{
  _ghost_stmt(unfold (Struct_packet.struct_packet_hole_buffer
    $(p) 1.0R $(saved)));
  p->header = x;
  _ghost_stmt(fold (Struct_packet.struct_packet_hole_buffer
    $(p) 1.0R { $(saved) with fld_header = $(x) }));
}

int read_nested_alias(_plain const struct envelope *p)
  _ghost_arg(struct envelope saved)
  _requires(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(p) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(p) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(return == saved.core.header)
{
  const struct packet *core = &p->core;
  return read_hole(core);
}

int read_trailer(const struct trailer *p)
  _ensures(return == p->counter)
{
  return p->counter;
}

int read_aliased_child(_plain const struct envelope *p)
  _ghost_arg(struct envelope saved)
  _requires(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(p) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(p) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(return == saved.core.trailer.counter)
{
  const struct packet *core = &p->core;
  _assert(_live(core));
  _ghost_stmt(unfold (Struct_packet.struct_packet_hole_buffer
    ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
    0.5R $(saved.core)));
  int result = read_trailer(&core->trailer);
  _ghost_stmt(fold (Struct_packet.struct_packet_hole_buffer
    ($(p) +! Struct_envelope.struct_envelope_offsetof_core)
    0.5R $(saved.core)));
  return result;
}

int read_whole(const struct envelope *p)
  _ensures(return == p->core.header)
{
  return p->core.header;
}

int read_live_alias(const struct envelope *p)
  _ensures(return == p->core.header)
{
  const struct packet *core = &p->core;
  _assert(_live(core));
  return core->header;
}

int read_spliced_alias(const struct envelope *p)
  _ensures(return == p->core.header)
{
  const struct packet *core = &p->core;
  _ghost_stmt(
    with address. assert ptr_pts_to $&(core) 1.0R address;
    assert pure (address == $(core)));
  return core->header;
}

void write_alias_after_join(struct envelope *p, bool choose)
  _ensures(p->core.header == 3)
{
  struct packet *core = &p->core;
  if (choose)
    _ensures(_live(core) && _live(*p))
  {
    core->header = 1;
  }
  else
  {
    core->header = 2;
  }
  core->header = 3;
}
