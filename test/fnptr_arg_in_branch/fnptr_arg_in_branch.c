// A function passed to a call statement inside an `if` arm.
//
// Decaying a function to an address seeds the fact of what the code there
// does (`is_valid`), for the callee. A callee that does not ask for it hands
// it straight back, so it has to be put down by the end of the arm --
// otherwise it is still held there, which the other arm does not hold, and
// the two cannot be joined.

#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

void done(int32_t x) _requires(x > 0) { }

// Registers a callback it does not call.
void later(void (*cb)(int32_t));

void register_if(bool c)
{
    if (c)
    {
        later(done);
    }
}

// The same with a local in scope, so the arm is not the function's own frame.
int32_t register_local(bool c)
{
    int32_t n = 1;
    if (c)
    {
        later(done);
    }
    else
    {
        n = 2;
    }
    return n;
}

// And in both arms, and again after the `if`.
void register_both(bool c)
{
    if (c)
    {
        later(done);
    }
    else
    {
        later(done);
        later(done);
    }
    later(done);
}
