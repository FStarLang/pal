#include "pal.h"
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

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

struct link {
  _plain struct link *next;
  _plain struct link *prev;
};

struct indexed_link {
  struct link node;
  size_t offset;
};

bool saved_link_matches(_plain const void *base, _plain struct link *q, size_t i)
  _ghost_arg(struct link *saved) _ghost_arg(size_t index)
  _preserves(_inline_pulse(ptr_pts_to ($(base) +! Struct_indexed_link.struct_indexed_link_offsetof_node
    +! Struct_link.struct_link_offsetof_next) 0.5R $(saved) **
    size_t_pts_to ($(base) +! Struct_indexed_link.struct_indexed_link_offsetof_offset) 0.5R $(index)))
  _ensures(_inline_pulse(pure ($(return) <==> ($(saved) == $(q) /\ $(index) == $(i)))))
{
  const struct indexed_link *p = base;
  _assert(_inline_pulse(ptr_pts_to $&(p->node.next) 0.5R $(saved)));
  _assert(_inline_pulse(size_t_pts_to $&(p->offset) 0.5R $(index)));
  return p->node.next == q && p->offset == i;
}

void unlink_front(_plain struct link *head, _plain struct link *replacement)
  _ghost_arg(struct link *first)
  _requires(_inline_pulse(ptr_pts_to ($(head) +! Struct_link.struct_link_offsetof_next) 1.0R $(first) **
    ptr_pts_to ($(first) +! Struct_link.struct_link_offsetof_prev) 1.0R $(head)))
  _ensures(_inline_pulse(ptr_pts_to ($(head) +! Struct_link.struct_link_offsetof_next) 1.0R $(replacement) **
    ptr_pts_to ($(first) +! Struct_link.struct_link_offsetof_prev) 1.0R $(replacement)))
{
  struct link *saved = head->next;
  head->next = replacement;
  saved->prev = replacement;
}

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

struct message {
  _plain const struct envelope *owner;
};

int read_message_holes(_plain struct message message, const struct envelope *whole)
  _ghost_arg(struct envelope saved)
  _requires(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(message.owner) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(message.owner) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(message.owner) 0.5R $(saved) **
    Struct_packet.struct_packet_hole_buffer
      ($(message.owner) +! Struct_envelope.struct_envelope_offsetof_core)
      0.5R $(saved.core)))
  _ensures(return == (saved.core.header ^ whole->core.header))
{
  _assert(_inline_pulse(Struct_envelope.struct_envelope_hole_core
    $(message.owner) 0.5R $(saved)));
  _assert(_inline_pulse(Struct_packet.struct_packet_hole_buffer
    $&(message.owner->core) 0.5R $(saved.core)));
  _ghost_stmt(unfold (Struct_packet.struct_packet_hole_buffer
    $&(message.owner->core) 0.5R $(saved.core)));
  const struct packet *core = &message.owner->core;
  _assert(_live(core));
  int result = core->header;
  int other = whole->core.header;
  _ghost_stmt(fold (Struct_packet.struct_packet_hole_buffer
    $&(message.owner->core) 0.5R $(saved.core)));
  return result ^ other;
}

int write_then_read_whole(struct trailer value, int x)
  _ensures(return == x)
{
  _ghost_stmt(Struct_trailer.struct_trailer_focus_counter $&(value));
  _assert(_inline_pulse(
    Struct_trailer.struct_trailer_hole_counter $&(value) 1.0R _));
  value.counter = x;
  _ghost_stmt(Struct_trailer.struct_trailer_unfocus_counter $&(value));
  _assert(_inline_pulse(
    Struct_trailer.struct_trailer_pts_to $&(value) 1.0R _));
  return value.counter;
}

int read_message_after_handback(_plain struct message message)
  _ghost_arg(struct envelope saved)
  _requires(_inline_pulse(
    Struct_envelope.struct_envelope_pts_to $(message.owner) 0.5R $(saved)))
  _ensures(_inline_pulse(
    Struct_envelope.struct_envelope_pts_to $(message.owner) 0.5R $(saved)))
  _ensures(return == saved.tag)
{
  _ghost_stmt(Struct_envelope.struct_envelope_focus_core $(message.owner));
  _assert(_inline_pulse(
    Struct_envelope.struct_envelope_hole_core $(message.owner) 0.5R $(saved)));
  _ghost_stmt(Struct_envelope.struct_envelope_unfocus_core $(message.owner));
  _assert(_inline_pulse(
    Struct_envelope.struct_envelope_pts_to $(message.owner) 0.5R $(saved)));
  return message.owner->tag;
}

int read_loaned_leaf(_plain struct message message)
  _ghost_arg(int x)
  _preserves(_inline_pulse(int32_t_pts_to
    (($(message.owner) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_header) 0.5R $(x)))
  _ensures(return == x)
{
  const struct packet *p = &message.owner->core;
  _assert(_inline_pulse(int32_t_pts_to $&(p->header) 0.5R $(x)));
  return p->header;
}

struct mutable_message {
  _plain struct envelope *owner;
};

union reply {
  int code;
  unsigned word;
};

struct response {
  int prefix;
  union reply result;
};

union response_storage {
  struct response message;
  unsigned char buffer[32];
};

int read_loaned_response(_plain const union response_storage *s)
  _ghost_arg(struct response saved)
  _preserves(_inline_pulse(Struct_response.struct_response_pts_to $(s) 0.5R $(saved)))
  _requires(_inline_pulse(pure (Union_reply.Union_reply_code? $(saved).Struct_response.fld_result)))
  _ensures(_inline_pulse(pure ($(saved).Struct_response.fld_result == Union_reply.Union_reply_code $(return))))
{
  _assert(_inline_pulse(Struct_response.struct_response_pts_to $&(s->message) 0.5R $(saved)));
  return s->message.result.code;
}

union reply read_reply(_plain const struct response *p)
  _ghost_arg(int code)
  _preserves(_inline_pulse(Union_reply.union_reply_pts_to
    ($(p) +! Struct_response.struct_response_offsetof_result) 0.5R (Union_reply.Union_reply_code $(code))))
  _ensures(_inline_pulse(pure ($(return) == Union_reply.Union_reply_code $(code))))
{
  _assert(_inline_pulse(Union_reply.union_reply_pts_to $&(p->result) 0.5R (Union_reply.Union_reply_code $(code))));
  return p->result;
}

struct trailer replace_loaned_trailer(_plain struct mutable_message message, struct trailer next)
  _ghost_arg(struct trailer before)
  _requires(_inline_pulse(Struct_trailer.struct_trailer_pts_to
    (($(message.owner) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_trailer) 1.0R $(before)))
  _ensures(_inline_pulse(Struct_trailer.struct_trailer_pts_to
    (($(message.owner) +! Struct_envelope.struct_envelope_offsetof_core)
      +! Struct_packet.struct_packet_offsetof_trailer) 1.0R $(next)))
  _ensures(return.counter == before.counter)
{
  _assert(_inline_pulse(Struct_trailer.struct_trailer_pts_to
    $&(message.owner->core.trailer) 1.0R $(before)));
  struct trailer old = message.owner->core.trailer;
  message.owner->core.trailer = next;
  return old;
}
