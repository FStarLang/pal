#include "pal.h"
#include <stdint.h>

void
DeclMultipleRequires(
    uint32_t Value
    )
    _requires(Value > 0)
    _requires(Value < 10);

void
DeclMultipleRequires(
    uint32_t OtherValue
    )
{
    // Both declaration preconditions should be available in the body.
    _assert(OtherValue < 10);
}
