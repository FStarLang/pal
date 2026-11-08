#include "pal.h"
#include <stdint.h>

// Variadic arguments are evaluated and dropped: whatever evaluating one obliges
// is still checked, which is what lets it be any expression (issue #354).

struct D { uint32_t irq; int32_t level; };

void log_msg(const _array char *fmt, ...);

void report(struct D *d)
  _preserves(_live(*d))
{
  log_msg("irq %d\n", d->irq);
}

void report_expr(uint32_t x)
{
  log_msg("val %d\n", x + 1);
}

// Signed arithmetic in an argument keeps its overflow obligation.
void report_level(struct D *d)
  _preserves(_live(*d))
  _requires(d->level < 100)
{
  log_msg("level %d %d\n", d->level + 1, d->irq);
}

uint32_t twice(uint32_t x)
  _requires(x < 1000)
  _ensures(return == 2 * x)
{
  return x + x;
}

void report_call(uint32_t x)
  _requires(x < 1000)
{
  int32_t n = 0;
  log_msg("%u\n", twice(x)), n = 1;
}
