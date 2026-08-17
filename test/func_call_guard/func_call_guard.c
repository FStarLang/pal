#include "pal.h"
#include <stdint.h>

/* Loop constructs with a function call directly in the guard/condition.
 *
 * Each pair below (`_call` / `_call_ref`) tests the same loop shape with a
 * guard call that either takes a plain `int` (`helper`) or borrows a
 * resource (`read_val`, a `const int *`).
 *
 * `do_while_call[_ref]` always verified: PAL's do-while desugaring moves
 * the guard call into a plain body assignment (via `_do_while_cond` +
 * a linking invariant, see test/do_while/do_while.c), so Pulse's actual
 * `while` condition is just a pure flag read.
 *
 * `while_call[_ref]` / `for_cond_call[_ref]` leave the call inline in
 * Pulse's `while (cond) { ... }` (a `for` loop desugars to a `while`).
 * Until https://github.com/FStarLang/FStar/pull/4433 landed, this failed
 * with `Error 339: Cannot find witness for exists* ...`, because PAL emits
 * every function as `divergent fn` and Pulse's while-checker didn't thread
 * that through the guard's checked type. All eight functions now verify.
 */

int helper(int x) _requires(x < 100) _ensures(return == x + 1) { return x + 1; }

int do_while_call(int n)
  _requires(n >= 1 && n <= 50)
{
  int i = 0;
  do
    _do_while_first(first)
    _do_while_cond(cont)
    _invariant(_live(i) && _live(first) && _live(cont))
    _invariant(first ==> i < n)
    _invariant(i <= n)
    _invariant(first || (cont == (i + 1 < n)))
  {
    i = i + 1;
  } while (helper(i) < n);
  return i;
}

int while_call(int n)
  _requires(n >= 0 && n <= 50)
{
  int i = 0;
  while (helper(i) < n)
    _invariant(_live(i))
    _invariant(i >= 0 && i <= n)
  {
    i = i + 1;
  }
  return i;
}

int for_cond_call(int n)
  _requires(n >= 0 && n <= 50)
{
  int i = 0;
  for (; helper(i) < n; )
    _invariant(_live(i))
    _invariant(i >= 0 && i <= n)
  {
    i = i + 1;
  }
  return i;
}

/* Same as `helper`, but borrows `&i` as a resource instead of taking an
 * `int` by value (matching test/const_read/const_read.c's `read_val`). */
int read_val(const int *x) _ensures(return == *x) { return *x; }

int do_while_call_ref(int n)
  _requires(n >= 1 && n <= 50)
{
  int i = 0;
  do
    _do_while_first(first)
    _do_while_cond(cont)
    _invariant(_live(i) && _live(first) && _live(cont))
    _invariant(first ==> i < n)
    _invariant(i <= n)
    _invariant(first || (cont == (i < n)))
  {
    i = i + 1;
  } while (read_val(&i) < n);
  return i;
}

int while_call_ref(int n)
  _requires(n >= 0 && n <= 50)
{
  int i = 0;
  while (read_val(&i) < n)
    _invariant(_live(i))
    _invariant(i >= 0 && i <= n)
  {
    i = i + 1;
  }
  return i;
}

int for_cond_call_ref(int n)
  _requires(n >= 0 && n <= 50)
{
  int i = 0;
  for (; read_val(&i) < n; )
    _invariant(_live(i))
    _invariant(i >= 0 && i <= n)
  {
    i = i + 1;
  }
  return i;
}

