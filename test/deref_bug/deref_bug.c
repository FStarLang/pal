#include "pal.h"
#include <stdint.h>

void bug_if(_plain int *p)
    _preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) 0l))
{
    if (1)
        _ensures(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) 0l))
    {
    }
    return;
}

void bug_match(_plain int *p)
    _preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) 0l))
{
    _ghost_stmt(
      match (true)
      ensures (Pulse.Lib.Reference.pts_to $(p) 0l)
      {
        true -> { () }
        false -> { () }
      }
    );
    return;
}
