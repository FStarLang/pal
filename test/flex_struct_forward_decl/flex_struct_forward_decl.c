/* A struct whose only use of a later-defined type is a flexible array member.

   `merge` hoists `struct table`'s definition to its forward declaration so
   that `table_count`'s prototype can find it, and then `reorder_type_deps`
   restores the order its fields need. That pass followed fixed arrays but not
   flexible ones, so `struct table` stayed ahead of `struct entry`, was skipped
   ("field `items` is an array"), and every function using a field of it went
   untranslated. Seen on a slab container in BOSS. */
#include "pal.h"
#include <stdint.h>

typedef struct table table;

uint32_t table_count(table *t)
    _ensures(return == t->count);

typedef struct entry { uint64_t key; uint32_t val; } entry;

struct table {
    uint32_t count;
    entry items[];
};

uint32_t table_count(table *t)
{
    return t->count;
}
