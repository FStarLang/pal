#include "pal.h"

union reply {
  int code;
  unsigned word;
};

struct response {
  int prefix;
  union reply result;
};

union reply read_without_loan(_plain const struct response *p)
  _preserves(_inline_pulse(int32_t_pts_to
    ($(p) +! Struct_response.struct_response_offsetof_prefix) 0.5R 0l))
{
  _assert(_inline_pulse(Union_reply.union_reply_pts_to $&(p->result) 0.5R
    (Union_reply.Union_reply_code 0l)));
  return p->result;
}
