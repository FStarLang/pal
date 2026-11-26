#include "pal.h"
#include <stdint.h>

union key { uint8_t bytes[4]; uint32_t word; };
struct rec { uint32_t kind; union key k; };

// The member initializer is the array value itself, as in a struct
// initializer: no array-to-pointer conversion.
void set_bytes(struct rec *r)
  _ensures(r->kind == 1)
  _ensures(_inline_pulse(pure ($(r->k) ==
    Union_key.Union_key_bytes (FStar.Seq.seq_of_list [1uy; 2uy; 0uy; 0uy]))))
{
  *r = (struct rec){ .kind = 1, .k = { .bytes = { 1, 2 } } };
}

struct page { uint32_t used; uint8_t data[4096]; };

// A zero byte array is one `Seq.create`, not a 4096-element list.
void clear_page(struct page *p)
  _ensures(p->used == 0)
  _ensures(_inline_pulse(pure (FStar.Seq.index $(p->data) 4095 == 0uy)))
{
  *p = (struct page){ .used = 0, .data = {0} };
}
