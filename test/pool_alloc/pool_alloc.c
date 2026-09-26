#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* Acceptance test 3 from `palow.md`: a custom allocator that takes a range of
 * bytes and hands out pointers into it, usable just like `malloc`.
 *
 * This is the program the whole design exists for. Under the old model a
 * block's ownership predicate names the type stored in it, so there is no way
 * to turn one allocation of N bytes into several independently owned typed
 * objects -- the program cannot even be stated. Here a block is bytes,
 * `mem_split` cuts it, and a chunk becomes a `uint32_t` object as soon as a
 * value can be exhibited for it. No new axiom is involved and the translator
 * has no idea a pool is what this is: everything below is ordinary annotated C
 * whose contracts happen to name the model's predicates.
 *
 * Note what the contracts do *not* say. A chunk arrives as a bare
 * `uint32_t_pts_to`, never as `Pulse.Lib.C.Palow.Alloc.freeable`, and `free`
 * spends exactly that -- so `free(p)` on a pool chunk is not merely bad
 * practice here, it is unprovable. That is the reason `freeable` does not
 * split, and it is why a pool that wants its chunks back publishes its own
 * release function (`pool_return` below) rather than borrowing `free`.
 *
 * `palow-only`: the old model has no vocabulary for any of this. The C is
 * still compiled, which is what keeps the annotations honest as no-ops. */

_include_pulse(Pool_shim,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar
  include Pulse.Lib.C.Palow.Encoding

  (* The bytes the pool still has to hand out. They are zeroed rather than
     uninitialised so that a chunk can be claimed at a value the moment it is
     carved -- which is what `calloc` gives and `malloc` does not, and is the
     difference between a pool whose chunks are readable and one whose chunks
     have to be written first. The size is a `nat` rather than a `size_t`
     because a contract term is typed with none of the `requires` in scope, so
     a refined subtraction would not typecheck there. *)
  unfold let pool_block (a: ptr) (n: nat) : slprop =
    mem_pts_to a 1.0R (zeroed n)

  (* Two zeroed ranges laid end to end are one zeroed range. This is what a
     chunk going back into the pool needs, and it is the only thing in this
     module that is not already in the model. *)
  let zeroed_append (m n: nat)
    : Lemma (append (zeroed m) (zeroed n) == zeroed (m + n))
            [SMTPat (append (zeroed m) (zeroed n))]
    = FStar.Seq.lemma_eq_elim (append (zeroed m) (zeroed n)) (zeroed (m + n))
)

/* Carve one `uint32_t` off the front of the block, leaving the caller the
 * tail. `rewrites_to` records that the chunk is at the block's own address,
 * which is what lets the caller go on talking about it in the words its own
 * contract used. */
_requires(_inline_pulse(Pool_shim.pool_block $(a) (FStar.SizeT.v $(rest) + 4)))
_ensures(_inline_pulse(rewrites_to $(return) $(a)))
_ensures(_inline_pulse(uint32_t_pts_to $(return) 1.0R 0ul))
_ensures(_inline_pulse(Pool_shim.pool_block ($(a) +! 4sz) (FStar.SizeT.v $(rest))))
uint32_t *pool_take(_plain uint8_t *a, size_t rest)
{
  _ghost_stmt(mem_split $(a) 4sz);
  _ghost_stmt(encode_zero 4);
  _ghost_stmt(uint32_t_claim $(a) 0ul);
  return (uint32_t *) a;
}

/* Give a chunk back. This is the pool's own release, and it is not `free`:
 * `free` needs `freeable`, which the pool never handed out, and this needs the
 * tail of the block, which `malloc` never hands out. Keeping the two rights
 * distinct is the point, not a limitation. */
_requires(_inline_pulse(uint32_t_pts_to $(p) 1.0R 0ul))
_requires(_inline_pulse(Pool_shim.pool_block ($(p) +! 4sz) (FStar.SizeT.v $(rest))))
_ensures(_inline_pulse(Pool_shim.pool_block $(p) (FStar.SizeT.v $(rest) + 4)))
void pool_return(_plain uint32_t *p, size_t rest)
{
  _ghost_stmt(uint32_t_reveal $(p));
  _ghost_stmt(encode_zero 4);
  _ghost_stmt(mem_join $(p) 4sz);
}

/* Two chunks out of one block, so that the objects really are independent:
 * each is owned separately and the tail is still a pool. */
_requires(_inline_pulse(Pool_shim.pool_block $(a) (FStar.SizeT.v $(rest) + 8)))
_ensures(_inline_pulse(uint32_t_pts_to $(a) 1.0R 0ul))
_ensures(_inline_pulse(uint32_t_pts_to ($(a) +! 4sz) 1.0R 0ul))
_ensures(_inline_pulse(Pool_shim.pool_block ($(a) +! 8sz) (FStar.SizeT.v $(rest))))
void pool_take2(_plain uint8_t *a, size_t rest)
{
  _ghost_stmt(encode_zero 4);
  _ghost_stmt(mem_split $(a) 4sz);
  _ghost_stmt(uint32_t_claim $(a) 0ul);
  _ghost_stmt(mem_split ($(a) +! 4sz) 4sz);
  _ghost_stmt(uint32_t_claim ($(a) +! 4sz) 0ul);
  /* The tail is at `(a + 4) + 4`, and the contract says `a + 8`. `add_add`
     makes the two equal; `rewrite each` is what says so to the matcher, which
     compares addresses syntactically. */
  _ghost_stmt(rewrite each (($(a) +! 4sz) +! 4sz) as ($(a) +! 8sz));
}

/* A chunk is an ordinary object: it is written through an ordinary pointer,
 * with no annotation saying where it came from. */
_requires(_inline_pulse(uint32_t_pts_to $(p) 1.0R 0ul))
_ensures(_inline_pulse(uint32_t_pts_to $(p) 1.0R $(v)))
void slot_set(_plain uint32_t *p, uint32_t v)
{
  *p = v;
}

/* And a client that uses the pool the way it would use `malloc`: take a
 * pointer, store through it, hand it back. */
_requires(_inline_pulse(Pool_shim.pool_block $(a) (FStar.SizeT.v $(rest) + 4)))
_ensures(_inline_pulse(uint32_t_pts_to $(a) 1.0R 5ul))
_ensures(_inline_pulse(Pool_shim.pool_block ($(a) +! 4sz) (FStar.SizeT.v $(rest))))
void pool_client(_plain uint8_t *a, size_t rest)
{
  uint32_t *p = pool_take(a, rest);
  slot_set(p, 5);
}
