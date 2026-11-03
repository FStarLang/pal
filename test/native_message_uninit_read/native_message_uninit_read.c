#include "pal.h"
#include <stdint.h>

struct message {
    _plain uint64_t *result;
};

uint64_t read_unwritten(_plain struct message message)
  _requires(_inline_pulse(uint64_t_pts_to_uninit $(message.result)))
  _ensures(_inline_pulse(uint64_t_pts_to_uninit $(message.result)))
{
    _assert(_inline_pulse(uint64_t_pts_to_uninit $(message.result)));
    return *message.result;
}
