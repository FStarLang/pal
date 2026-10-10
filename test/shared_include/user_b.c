#include "vocab.h"

// A second translation unit using the same shared module. It never mentions
// `sign` itself, so if the include's body were not scanned for dependencies
// the generated declaration `sign` depends on would be pruned away and the
// module would refer to a module that was not emitted.
int use_clamp(int x)
    _ensures(_inline_pulse(pure (Vocab.nonneg $(return))))
{
    return clamp(x);
}
