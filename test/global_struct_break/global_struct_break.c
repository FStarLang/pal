#include "pal.h"
#include <stdint.h>

struct domain {
  uint64_t sweeping_done;
  uint64_t work;
};

struct domain *state;

void finish_sweeping(void)
  _requires(_live(state) && _live(*state))
  _ensures(_live(state) && _live(*state))
{
  if (state->sweeping_done) return;
  while (!state->sweeping_done)
    _invariant(_live(state) && _live(*state))
    _ensures(1 == 1)
  {
    state->sweeping_done = 1;
    break;
  }
}

/* A natural exit need not satisfy any of the break postconditions. */
void finish_work(void)
  _requires(_live(state) && _live(*state))
  _ensures(_live(state) && _live(*state))
  _ensures(state->work == 0)
{
  while (state->work)
    _invariant(_live(state) && _live(*state))
    _ensures(0 == 1)
  {
    state->work = 0;
  }
}

/* Inner breaks must not exit the outer loop; continue still uses its invariant. */
void finish_nested(void)
  _requires(_live(state) && _live(*state))
  _ensures(_live(state) && _live(*state))
  _ensures(state->sweeping_done != 0)
{
  while (!state->sweeping_done)
    _invariant(_live(state) && _live(*state))
    _ensures(state->sweeping_done == 1)
    _ensures(state->sweeping_done == 2)
  {
    while (state->work)
      _invariant(_live(state) && _live(*state))
      _ensures(state->work == 0)
    {
      state->work = 0;
      break;
    }
    state->sweeping_done = 1;
    break;
  }
  while (state->work)
    _invariant(_live(state) && _live(*state))
    _invariant(state->sweeping_done != 0)
    _ensures(0 == 1)
  {
    state->work = 0;
    continue;
  }
}

/* Neither the guard-false alternative nor the break postcondition holds. */
void invalid_break(void)
  _requires(_live(state) && _live(*state))
  _ensures(_live(state) && _live(*state))
{
  while (!state->sweeping_done)
    _invariant(_live(state) && _live(*state))
    _ensures(state->work == 2)
  {
    state->work = 1;
    break;
  }
}
