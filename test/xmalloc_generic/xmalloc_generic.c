#include "pal.h"
#include <stdlib.h>

/* Acceptance test 1 from `palow.md`, in its general form: "`malloc` is no
   longer a special built-in; we can give a spec to a custom `xmalloc`
   function and use it just like `malloc` today."

   `test/xmalloc` gives a spec to a *typed* constructor, which is already more
   than the old model could do. This file is the harder version and the one
   the acceptance test asks for: a `void *xmalloc(size_t n)` that knows
   nothing about what its caller will store, and a client that uses it exactly
   where it would have written `malloc`.

   The old model cannot state this contract at all. There a block's ownership
   predicate names the type stored in it, so there is no proposition for
   "`n` bytes of storage, contents unspecified, yours to free" -- the return
   type would have to be `T *` for some `T` the allocator does not know. In
   Palow that proposition is just `mem_pts_to` at `uninit n` plus `freeable`,
   which is what `Xm.block` below says, and the caller claims those bytes at
   whatever type it likes. */

_include_pulse(Xm,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Alloc

  unfold let block (a: ptr) (n: FStar.SizeT.t) : slprop =
    mem_pts_to a 1.0R (uninit (FStar.SizeT.v n)) ** freeable a n
)

/* A postcondition of `0` is false, so there is no state this function could
   return in: it does not return. That is all `_Noreturn` means, said in the
   vocabulary the contract already has. */
_ensures(0)
void xabort(void);

/* The allocator. `_allocated` on a `void *` return says the caller gets a
   block to free; the `_ensures` says how big it is and that its contents are
   unspecified. Together they are exactly `malloc`'s own contract minus the
   possibility of failure -- which is the whole point of `xmalloc`. */
_ensures(_inline_pulse(Xm.block $(return) $(n)))
_allocated void *xmalloc(size_t n)
{
    void *p = malloc(n);
    if (p == NULL) {
        xabort();
    }
    return p;
}

/* The client. Nothing here is written differently than it would be against
   `malloc`, except that it does not have to check for failure. */
void client(void)
{
    int *i = xmalloc(sizeof(int));
    *i = 6;
    (*i)++;
    free(i);
}
