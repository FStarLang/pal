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
 * `mem_split_at` cuts it, and a chunk is readable as a `uint32_t` when its
 * actual effective index permits that access and its zero representation is
 * known. A ghost claim does not install a type. No new axiom is involved and the translator
 * has no idea a pool is what this is: everything below is ordinary annotated C
 * whose contracts happen to name the model's predicates.
 *
 * Note what the contracts do *not* say. A chunk arrives as a bare
 * `uint32_t_pts_to`, never as `Pulse.Lib.C.Palow.Alloc.freeable`, and `free`
 * spends exactly that -- so `free(p)` on a pool chunk is not merely bad
 * practice here, it is unprovable. That is the reason `freeable` does not
 * split, and it is why a pool that wants its chunks back publishes its own
 * release function (`pool_return` below) rather than borrowing `free`. */

_include_pulse(Pool_shim,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar
  include Pulse.Lib.C.Palow.Encoding
  module ET = Pulse.Lib.C.Palow.Etype
  module Seq = FStar.Seq
  module SZ = FStar.SizeT
  module Math = FStar.Math.Lemmas

  (* The bytes the pool still has to hand out. They are zeroed rather than
     uninitialised so that a chunk can be claimed at a value the moment it is
     carved -- which is what `calloc` gives and `malloc` does not, and is the
     difference between a pool whose chunks are readable and one whose chunks
     have to be written first. The size is a `nat` rather than a `size_t`
     because a contract term is typed with none of the `requires` in scope, so
     a refined subtraction would not typecheck there. *)
  (* The pool promises scalar access to each four-byte slot, without hiding
     an incompatible index or establishing a nominal type from zero bytes. *)
  let slot_read_ok (e: ET.etypes) : prop =
    forall (k: nat). k < ET.elen e ==>
      (match ET.eget e k with
       | None -> True
       | Some en -> b2t (ET.access_ok en.ET.ty (en.ET.off - k % 4) uint32_t_ctype))

  unfold let pool_block (a: ptr) (n: nat) : slprop =
    exists* e. mem_pts_to_at a 1.0R (zeroed n) e **
      pure (ET.elen e == n /\ slot_read_ok e /\ aligned a uint32_t_alignof)

  let split_guard (e: ET.etypes)
    : Lemma
        (requires 4 <= ET.elen e /\ slot_read_ok e)
        (ensures ET.read_ok (Seq.slice e 0 4) uint32_t_ctype
                 /\ slot_read_ok (Seq.slice e 4 (ET.elen e)))
    = let tail (k: nat) : Lemma (k < ET.elen e - 4 ==>
        (match ET.eget (Seq.slice e 4 (ET.elen e)) k with
         | None -> True
         | Some en -> b2t (ET.access_ok en.ET.ty
             (en.ET.off - k % 4) uint32_t_ctype))) =
        if k < ET.elen e - 4 then begin
          let readable = match ET.eget e (4 + k) with
            | None -> True
            | Some en -> b2t (ET.access_ok en.ET.ty
                (en.ET.off - (4 + k) % 4) uint32_t_ctype) in
          assert readable;
          Math.modulo_distributivity k 4 4
        end
      in Classical.forall_intro tail

  let join_guard (head tail: ET.etypes)
    : Lemma
        (requires ET.read_ok head uint32_t_ctype /\ slot_read_ok tail)
        (ensures slot_read_ok (Seq.append head tail))
    = let aux (k: nat) : Lemma (k < ET.elen head + ET.elen tail ==>
        (match ET.eget (Seq.append head tail) k with
         | None -> True
         | Some en -> b2t (ET.access_ok en.ET.ty
             (en.ET.off - k % 4) uint32_t_ctype))) =
        if k < ET.elen head + ET.elen tail then
          if k < 4 then () else begin
            let readable = match ET.eget tail (k - 4) with
              | None -> True
              | Some en -> b2t (ET.access_ok en.ET.ty
                  (en.ET.off - (k - 4) % 4) uint32_t_ctype) in
            assert readable;
            Math.modulo_distributivity (k - 4) 4 4
          end
      in Classical.forall_intro aux

  let zeroed_append (m n: nat)
    : Lemma (append (zeroed m) (zeroed n) == zeroed (m + n))
            [SMTPat (append (zeroed m) (zeroed n))]
    = FStar.Seq.lemma_eq_elim (append (zeroed m) (zeroed n)) (zeroed (m + n))

  ghost fn take (a: ptr) (rest: SZ.t)
    requires pool_block a (SZ.v rest + 4)
    ensures uint32_t_pts_to a 1.0R 0ul **
      pool_block (a +! 4sz) (SZ.v rest)
  {
    with e. assert mem_pts_to_at a 1.0R (zeroed (SZ.v rest + 4)) e;
    split_guard e;
    mem_split_at a 4sz;
    aligned_add a uint32_t_alignof 4sz;
    encode_zero 4;
    uint32_t_claim a 0ul;
    fold pool_block (a +! 4sz) (SZ.v rest);
  }

  ghost fn give_back (a: ptr) (rest: SZ.t)
    requires uint32_t_pts_to a 1.0R 0ul **
      pool_block (a +! 4sz) (SZ.v rest)
    ensures pool_block a (SZ.v rest + 4)
  {
    uint32_t_reveal a;
    with b head. assert mem_pts_to_at a 1.0R b head;
    with tail. assert mem_pts_to_at (a +! 4sz) 1.0R (zeroed (SZ.v rest)) tail;
    join_guard head tail;
    encode_zero 4;
    mem_join_at a 4sz;
    zeroed_append 4 (SZ.v rest);
    fold pool_block a (SZ.v rest + 4);
  }
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
  _ghost_stmt(Pool_shim.take $(a) $(rest));
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
  _ghost_stmt(Pool_shim.give_back $(p) $(rest));
}

/* Two chunks out of one block, so that the objects really are independent:
 * each is owned separately and the tail is still a pool. */
_requires(_inline_pulse(Pool_shim.pool_block $(a) (FStar.SizeT.v $(rest) + 8)))
_ensures(_inline_pulse(uint32_t_pts_to $(a) 1.0R 0ul))
_ensures(_inline_pulse(uint32_t_pts_to ($(a) +! 4sz) 1.0R 0ul))
_ensures(_inline_pulse(Pool_shim.pool_block ($(a) +! 8sz) (FStar.SizeT.v $(rest))))
void pool_take2(_plain uint8_t *a, size_t rest)
{
  _ghost_stmt(with e. assert mem_pts_to_at $(a) 1.0R
    (zeroed (FStar.SizeT.v $(rest) + 8)) e);
  _ghost_stmt(mem_pts_to_at_fits $(a));
  _ghost_stmt(FStar.SizeT.fits_lte (FStar.SizeT.v $(rest) + 4)
    (addr_of $(a) + FStar.SizeT.v $(rest) + 8));
  _ghost_stmt(fold Pool_shim.pool_block $(a) (FStar.SizeT.v $(rest) + 8));
  _ghost_stmt(Pool_shim.take $(a) ($(rest) `FStar.SizeT.add` 4sz));
  /* `divides_addr` is opaque, so stepping four bytes on from an aligned
     address is a lemma call rather than something the solver does itself. */
  _ghost_stmt(aligned_add $(a) uint32_t_alignof 4sz);
  _ghost_stmt(aligned_add $(a) uint32_t_alignof 8sz);
  _ghost_stmt(Pool_shim.take ($(a) +! 4sz) $(rest));
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
