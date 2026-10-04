#ifndef TAGGED_H
#define TAGGED_H

#include <stdint.h>

struct tagged {
  uint8_t tag;
  uint64_t value;
};

#endif
