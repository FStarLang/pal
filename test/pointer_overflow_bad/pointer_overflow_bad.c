#include "pal.h"
#include <stdint.h>

// Unbounded addition plus a bound on every address would prove False.
_include_pulse(Pointer_overflow_unsound,
  let rec advance (a: ptr) (n: nat)
    : GTot (p: ptr { addr_of p == addr_of a + n })
      (decreases n)
    = if n = 0 then a
      else
        let p = advance a (n - 1) in
        addr_of_add p 1sz;
        p +! 1sz

  let contradiction () : Lemma False =
    let top = advance null 18446744073709551616 in
    addr_bound top
)

void cannot_prove_false(void)
{
  _ghost_stmt(Pointer_overflow_unsound.contradiction ());
}
