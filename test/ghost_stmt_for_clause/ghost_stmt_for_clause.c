#include "pal.h"
#include <stdint.h>

/* Ghost steps in `for` clauses.
 *
 * A `for` init/increment clause is a comma expression, so a ghost step used
 * there must expand to something valid as an *expression*. Under C2PULSE both
 * macros expand to a statement expression `({ ... })`, which is fine; the
 * plain-C `#else` branch has to be a null expression rather than nothing at
 * all, or the compiler sees `for ( , ctr = 0; ...`.
 *
 * F* only ever sees the C2PULSE branch, so this verifies either way -- the
 * defect is compile-only, which is what the `compile` target catches.
 *
 * The loop variable is declared beforehand: a declaration cannot appear in a
 * comma expression, so the init clause has to be a plain assignment.
 */

/* `_ghost_stmt` in the init and increment clauses, plus both macros in
 * statement position so the previously-working spellings stay covered. */
uint32_t ghost_in_for_clause(uint32_t x, uint32_t y)
  _requires((_specint) x * y <= UINT32_MAX)
  _ensures(return == x * y)
{
  uint32_t acc = 0;
  uint32_t ctr;
  _ghost_stmt(assert pure (0 == 0));
  for (_ghost_stmt(assert pure (0 == 0)), ctr = 0;
       ctr < x;
       _ghost_stmt(assert pure (0 == 0)), ctr = ctr + 1)
    _invariant(_live(ctr) && _live(acc))
    _invariant(ctr <= x && acc == ctr * y)
  {
    acc = acc + y;
  }
  _assert(acc == x * y);
  return acc;
}

/* `_assert` has the same defect for the same reason. */
uint32_t assert_in_for_clause(uint32_t x, uint32_t y)
  _requires((_specint) x * y <= UINT32_MAX)
  _ensures(return == x * y)
{
  uint32_t acc = 0;
  uint32_t ctr;
  for (_assert(acc == 0), ctr = 0;
       ctr < x;
       _assert(ctr < x), ctr = ctr + 1)
    _invariant(_live(ctr) && _live(acc))
    _invariant(ctr <= x && acc == ctr * y)
  {
    acc = acc + y;
  }
  return acc;
}

