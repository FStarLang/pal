#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct config {
    uint32_t tag;
    void *descriptor;
    size_t size;
};

struct view {
    uint32_t tag;
    size_t size;
};

struct view init_view(const struct config *cfg)
  _ensures(return.tag == cfg->tag)
  _ensures(return.size == cfg->size)
{
    struct view view = {0};
    view.tag = cfg->tag;
    view.size = cfg->size;
    return view;
}

struct view wrap(void *descriptor, size_t size)
  _ensures(return.tag == 7)
  _ensures(return.size == size)
{
    struct view view = init_view(&(struct config){
        .tag = 7,
        .descriptor = descriptor,
        .size = size,
    });
    return view;
}
