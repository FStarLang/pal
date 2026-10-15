#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

// Packed structs whose fields are still naturally aligned (issue #353).

struct __attribute__((packed)) hdr { uint8_t status; uint8_t pad; uint16_t len; };

uint16_t get_len(struct hdr *h)
  _preserves(_live(*h))
  _ensures(return == h->len)
{
  return h->len;
}

uint16_t local_hdr(void)
  _ensures(return == 7)
{
  struct hdr h;
  h.status = 0; h.pad = 0; h.len = 7;
  return h.len;
}

// C's alignment, which is also the one the proofs use.
size_t hdr_align(void)
  _ensures(return == 1)
{
  return _Alignof(struct hdr);
}

struct frame { uint16_t kind; struct hdr h; uint32_t crc; };

void set_frame(struct frame *f)
  _preserves(_live(*f))
  _ensures(f->h.len == 3)
{
  f->h.len = 3;
}

uint16_t heap_hdr(void)
{
  struct hdr *h = malloc(sizeof(struct hdr));
  if (!h) return 0;
  h->status = 1; h->pad = 0; h->len = 9;
  uint16_t r = h->len;
  free(h);
  return r;
}
