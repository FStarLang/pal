#include "pal.h"

/* Demonstrates how to verify branches that are definitely unreachable.
   The dead continuation still needs a typed ownership witness.
   Its contradictory path condition justifies rewriting emp to live p. */
_ensures(return == 7)
int unreachable_read(_plain int *p)
{
  if (1)
    return 7;

  _ghost_stmt(rewrite emp as live $(p));
  return *p;
  /* PAL places trailing ghost statements before the generated return. */
  _ghost_stmt(rewrite (live $(p)) as emp);
}

_ensures(return == 7)
int call_unreachable(_plain int *p)
{
  return unreachable_read(p);
}

/* The reachable dereference must receive real ownership from its caller. */
_preserves(_inline_pulse(
  if int32_to_bool $(skip) then emp else Pulse.Lib.Reference.pts_to $(p) 42l))
_ensures(return == (skip ? 7 : 42))
int conditional_read(int skip, _plain int *p)
{
  if (skip)
    return 7;

  _ghost_stmt(rewrite
    (if int32_to_bool $(skip) then emp else Pulse.Lib.Reference.pts_to $(p) 42l)
    as (Pulse.Lib.Reference.pts_to $(p) 42l));
  return *p;
  _ghost_stmt(rewrite (Pulse.Lib.Reference.pts_to $(p) 42l) as
    (if int32_to_bool $(skip) then emp else Pulse.Lib.Reference.pts_to $(p) 42l));
}

_ensures(return == 7)
int call_skipped(_plain int *p)
{
  _ghost_stmt(rewrite emp as
    (if int32_to_bool 1l then emp else Pulse.Lib.Reference.pts_to $(p) 42l));
  return conditional_read(1, p);
  _ghost_stmt(rewrite
    (if int32_to_bool 1l then emp else Pulse.Lib.Reference.pts_to $(p) 42l) as emp);
}

_ensures(return == 42)
int call_owned(void)
{
  int value = 42;
  _ghost_stmt(rewrite (Pulse.Lib.Reference.pts_to $(&value) 42l) as
    (if int32_to_bool 0l then emp else Pulse.Lib.Reference.pts_to $(&value) 42l));
  int result = conditional_read(0, &value);
  _ghost_stmt(rewrite
    (if int32_to_bool 0l then emp else Pulse.Lib.Reference.pts_to $(&value) 42l)
    as (Pulse.Lib.Reference.pts_to $(&value) 42l));
  _assert(value == 42);
  return result;
}
