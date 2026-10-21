#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

typedef enum state {
    state_idle = 0,
    state_write = 2,
    state_write_split = 6,
} state;

struct staged {
    state tag;
    uint32_t bytes;
};

struct parser {
    struct staged staged;
};

void stage_write(struct parser *parser, uint32_t bytes, bool split)
  _ensures(parser->staged.bytes == bytes)
  _ensures(parser->staged.tag == (split ? state_write_split : state_write))
{
    parser->staged = (struct staged){
        .tag = split ? state_write_split : state_write,
        .bytes = bytes,
    };
}
