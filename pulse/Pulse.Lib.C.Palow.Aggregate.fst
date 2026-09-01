module Pulse.Lib.C.Palow.Aggregate

(* ---------------------------------------------------------------------------
   Aggregates, worked out on one concrete struct.

   struct S { uint32_t f; uint8_t g; };   // sizeof 8, offsetof g == 4

   This module is the load-bearing test of the layer-0 interface: if field
   split/join for a struct with padding can be *proved* from `mem_split` and
   `mem_join`, then PAL can generate these lemmas per struct instead of
   axiomatizing an ownership predicate per struct as it does today.

   Two things worth noticing in the definitions below:

   - `struct_S_repr` says nothing at all about bytes 5..8. They are padding, and
     C leaves their contents unspecified. Because `struct_S_pts_to`
     existentially quantifies the byte range, this automatically means that
     writing a whole struct havocs its padding, and that no client can stash
     data there and expect it to survive -- which is the correct C semantics,
     obtained for free rather than by an extra rule.

   - The representation of a struct is therefore *not* unique, unlike the scalar
     case. That is exactly why layer 1 predicates are existential in general.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

noeq type struct_S = { f: U32.t; g: U8.t }

let struct_S_sizeof : SZ.t = 8sz
let struct_S_alignof : SZ.t = 4sz
let struct_S_offsetof_f : SZ.t = 0sz
let struct_S_offsetof_g : SZ.t = 4sz

(* Where the padding starts, and how much of it there is. *)
let struct_S_padoff : SZ.t = 5sz
let struct_S_padlen : SZ.t = 3sz

let struct_S_repr (x: struct_S) (b: bytes) : prop =
  len b == SZ.v struct_S_sizeof /\
  (len b == SZ.v struct_S_sizeof ==>
     (uint32_t_repr x.f (slice b 0 4) /\ uint8_t_repr x.g (slice b 4 5)))

let struct_S_pts_to ([@@@mkey] a: ptr) (p: perm) (x: struct_S) : slprop =
  exists* b. mem_pts_to a p b ** pure (struct_S_repr x b)

(* Ownership of the padding, which the split hands back separately so that the
   join can put the struct together again. *)
let struct_S_padding ([@@@mkey] a: ptr) (p: perm) : slprop =
  exists* pad. mem_pts_to (a +! struct_S_padoff) p pad
            ** pure (len pad == SZ.v struct_S_padlen)

(* ---------------------------------------------------------------------------
   Pure representation lemmas
   --------------------------------------------------------------------------- *)

let struct_S_repr_elim (x: struct_S) (b: bytes)
  : Lemma (requires struct_S_repr x b)
          (ensures  len b == 8 /\
                    slice b 0 4 == encode 4 None (U32.v x.f) /\
                    slice b 4 5 == encode 1 None (U8.v x.g))
  = ()

(* Reassembling a struct's byte range from its two fields and its padding. The
   `Seq.lemma_eq_intro`s are what tie `append` back to `slice`. *)
#push-options "--z3rlimit 40"
let struct_S_repr_intro (x: struct_S) (bf bg bpad: bytes)
  : Lemma (requires uint32_t_repr x.f bf /\ uint8_t_repr x.g bg /\
                    len bpad == SZ.v struct_S_padlen)
          (ensures  struct_S_repr x (append bf (append bg bpad)))
  = let b = append bf (append bg bpad) in
    Seq.lemma_eq_intro (slice b 0 4) bf;
    Seq.lemma_eq_intro (slice b 4 5) bg
#pop-options

(* `(a + 4) + 1` and `a + 5` are the same pointer. Proved via `ptr_ext` rather
   than left to the `add_add` SMT pattern, because that would additionally
   require the prover to see through `size_t` addition. *)
let struct_S_padptr (a: ptr)
  : Lemma ((a +! 4sz) +! 1sz == a +! struct_S_padoff)
  = addr_of_add a 4sz;
    addr_of_add (a +! 4sz) 1sz;
    addr_of_add a struct_S_padoff;
    ptr_ext ((a +! 4sz) +! 1sz) (a +! struct_S_padoff)

(* ---------------------------------------------------------------------------
   Field split and join

   Proved, not assumed: this is the whole point of the exercise.
   --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 40"
ghost fn struct_S_split (a: ptr) (#p: perm) (#x: struct_S)
  requires struct_S_pts_to a p x
  ensures  uint32_t_pts_to a p x.f
  ensures  uint8_t_pts_to (a +! struct_S_offsetof_g) p x.g
  ensures  struct_S_padding a p
{
  unfold struct_S_pts_to a p x;
  with b. assert (mem_pts_to a p b ** pure (struct_S_repr x b));
  struct_S_repr_elim x b;

  mem_split a 4sz;
  Seq.lemma_eq_intro (slice b 0 4) (encode 4 None (U32.v x.f));
  fold uint32_t_pts_to a p x.f;

  mem_split (a +! 4sz) 1sz;
  Seq.slice_slice b 4 8 0 1;
  Seq.lemma_eq_intro (slice (slice b 4 (len b)) 0 1) (encode 1 None (U8.v x.g));
  fold uint8_t_pts_to (a +! struct_S_offsetof_g) p x.g;

  Seq.slice_slice b 4 8 1 4;
  struct_S_padptr a;
  rewrite (mem_pts_to ((a +! 4sz) +! 1sz) p
                      (slice (slice b 4 (len b)) 1 (len (slice b 4 (len b)))))
       as (mem_pts_to (a +! struct_S_padoff) p (slice b 5 8));
  fold struct_S_padding a p;
}
#pop-options

#push-options "--z3rlimit 40"
ghost fn struct_S_join (a: ptr) (#p: perm) (#x: struct_S)
  requires uint32_t_pts_to a p x.f
  requires uint8_t_pts_to (a +! struct_S_offsetof_g) p x.g
  requires struct_S_padding a p
  ensures  struct_S_pts_to a p x
{
  unfold uint32_t_pts_to a p x.f;
  unfold uint8_t_pts_to (a +! struct_S_offsetof_g) p x.g;
  unfold struct_S_padding a p;
  with pad. assert (mem_pts_to (a +! struct_S_padoff) p pad);

  struct_S_padptr a;
  rewrite (mem_pts_to (a +! struct_S_padoff) p pad)
       as (mem_pts_to ((a +! 4sz) +! 1sz) p pad);
  rewrite (mem_pts_to (a +! struct_S_offsetof_g) p (encode 1 None (U8.v x.g)))
       as (mem_pts_to (a +! 4sz) p (encode 1 None (U8.v x.g)));

  mem_join (a +! 4sz) #p #(encode 1 None (U8.v x.g)) #pad 1sz;
  mem_join a #p #(encode 4 None (U32.v x.f)) #(append (encode 1 None (U8.v x.g)) pad) 4sz;

  struct_S_repr_intro x (encode 4 None (U32.v x.f)) (encode 1 None (U8.v x.g)) pad;
  fold struct_S_pts_to a p x;
}
#pop-options
