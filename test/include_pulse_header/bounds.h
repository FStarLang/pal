#include "pal.h"
#include <stdint.h>

// An `_include_pulse` block in a HEADER, named only from verbatim F* in the
// including file.  PAL prunes header declarations the main file does not
// reach, and verbatim F* used to contribute no dependency at all, so this
// module was silently dropped and every use of it failed with "Module name
// HeaderBounds could not be resolved".
_include_pulse(HeaderBounds,
  let under (n: nat) (x: FStar.UInt32.t) : prop = FStar.UInt32.v x < n
)

// Never named by the main file: must still be pruned.
_include_pulse(UnusedBounds,
  let never : nat = 0
)
