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
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Machine

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
  uint32_t_conceal a #p #_ #x.f;

  mem_split (a +! 4sz) 1sz;
  Seq.slice_slice b 4 8 0 1;
  Seq.lemma_eq_intro (slice (slice b 4 (len b)) 0 1) (encode 1 None (U8.v x.g));
  uint8_t_conceal (a +! struct_S_offsetof_g) #p #_ #x.g;

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
  uint32_t_reveal a #p #x.f;
  uint8_t_reveal (a +! struct_S_offsetof_g) #p #x.g;
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

(* ---------------------------------------------------------------------------
   A second struct, this time without padding.

   struct T { uint32_t y; uint32_t z; };   // sizeof 8, offsets 0 and 4

   Two reasons it is here. First, it is the shape PAL will generate in the
   common case, and it shows that the padding machinery above is not on the
   critical path when there is no padding: the split is two `mem_split`s and
   nothing else. Second, it is the struct member of the union in
   `Pulse.Lib.C.Palow.Union`, which is where the type-punning acceptance test
   lives.

   Note that `struct_T`'s representation *is* unique -- there are no padding
   bytes to be unconstrained -- so the existential in `struct_T_pts_to` is
   redundant here. It is kept anyway, because PAL cannot know in general
   whether a struct has padding without inspecting clang's layout, and a
   uniform shape is worth more than saving one existential.
   --------------------------------------------------------------------------- *)

noeq type struct_T = { y: U32.t; z: U32.t }

let struct_T_sizeof : SZ.t = 8sz
let struct_T_alignof : SZ.t = 4sz
let struct_T_offsetof_y : SZ.t = 0sz
let struct_T_offsetof_z : SZ.t = 4sz

let struct_T_repr (x: struct_T) (b: bytes) : prop =
  len b == SZ.v struct_T_sizeof /\
  (len b == SZ.v struct_T_sizeof ==>
     (uint32_t_repr x.y (slice b 0 4) /\ uint32_t_repr x.z (slice b 4 8)))

let struct_T_pts_to ([@@@mkey] a: ptr) (p: perm) (x: struct_T) : slprop =
  exists* b. mem_pts_to a p b ** pure (struct_T_repr x b)

let struct_T_repr_intro (x: struct_T) (b_y b_z: bytes)
  : Lemma (requires uint32_t_repr x.y b_y /\ uint32_t_repr x.z b_z)
          (ensures  struct_T_repr x (append b_y b_z))
  = let b = append b_y b_z in
    Seq.lemma_eq_intro (slice b 0 4) b_y;
    Seq.lemma_eq_intro (slice b 4 8) b_z

ghost fn struct_T_split (a: ptr) (#p: perm) (#x: struct_T)
  requires struct_T_pts_to a p x
  ensures  uint32_t_pts_to a p x.y
  ensures  uint32_t_pts_to (a +! struct_T_offsetof_z) p x.z
{
  unfold struct_T_pts_to a p x;
  with b. assert (mem_pts_to a p b ** pure (struct_T_repr x b));
  mem_split a 4sz;
  Seq.lemma_eq_intro (slice b 0 4) (encode 4 None (U32.v x.y));
  Seq.lemma_eq_intro (slice b 4 (len b)) (encode 4 None (U32.v x.z));
  uint32_t_conceal a #p #_ #x.y;
  uint32_t_conceal (a +! struct_T_offsetof_z) #p #_ #x.z;
}

ghost fn struct_T_join (a: ptr) (#p: perm) (#x: struct_T)
  requires uint32_t_pts_to a p x.y
  requires uint32_t_pts_to (a +! struct_T_offsetof_z) p x.z
  ensures  struct_T_pts_to a p x
{
  uint32_t_reveal a #p #x.y;
  uint32_t_reveal (a +! struct_T_offsetof_z) #p #x.z;
  rewrite (mem_pts_to (a +! struct_T_offsetof_z) p (encode 4 None (U32.v x.z)))
       as (mem_pts_to (a +! 4sz) p (encode 4 None (U32.v x.z)));
  mem_join a #p #(encode 4 None (U32.v x.y)) #(encode 4 None (U32.v x.z)) 4sz;
  struct_T_repr_intro x (encode 4 None (U32.v x.y)) (encode 4 None (U32.v x.z));
  fold struct_T_pts_to a p x;
}

(* ---------------------------------------------------------------------------
   Flexible array members

   struct V { uint32_t n; uint32_t data[]; };   // sizeof 4, data at offset 4

   Today this needs a dedicated `ExprT::MallocFlex` in the translator and a
   ghost `array_spec` field pinned inside the struct's F* record. Here it needs
   nothing: the header is an ordinary struct and the tail is an
   `array_pts_to` at offset `sizeof(header)`. There is no `struct_V_repr` at
   all, because the two parts are separately owned and never have to be
   described by a single byte range.

   The `pure` conjunct is the length refinement that PAL's `_refines` attribute
   expresses today; it is an ordinary proposition here rather than something
   the struct predicate has to be taught about.
   --------------------------------------------------------------------------- *)

let struct_V_sizeof : SZ.t = 4sz
let struct_V_offsetof_data : SZ.t = 4sz

let struct_V_pts_to ([@@@mkey] a: ptr) (p: perm) (n: U32.t) (xs: Seq.seq U32.t) : slprop =
  uint32_t_pts_to a p n
  ** array_pts_to uint32_t_repr (SZ.v uint32_t_sizeof) (a +! struct_V_offsetof_data) p xs
  ** pure (U32.v n == Seq.length xs)

(* Bridging the generic element view and the scalar points-to. `uint32_t_repr x b`
   is by definition `b == encode 4 None (U32.v x)`, so both directions are a
   fold/unfold pair; PAL emits one such pair per scalar type. *)
ghost fn uint32_t_of_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to uint32_t_repr a p x
  ensures  uint32_t_pts_to a p x
{
  unfold elem_pts_to uint32_t_repr a p x;
  uint32_t_conceal a #p #_ #x;
}

ghost fn uint32_t_to_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  elem_pts_to uint32_t_repr a p x
{
  uint32_t_reveal a #p #x;
  fold elem_pts_to uint32_t_repr a p x;
}

(* `return v->data[i];` -- the whole point of the flexible-array encoding is
   that this is an ordinary indexed read, so it goes through `array_focus` and
   nothing else. The four lines after the read are the inverse of the three
   before it, putting the array back together. *)
#push-options "--z3rlimit 30"
fn struct_V_get (a: ptr) (#p: perm) (#n: erased U32.t) (#xs: Seq.seq U32.t)
                (i: SZ.t { SZ.v i < Seq.length xs })
                (off: SZ.t { SZ.v off == SZ.v uint32_t_sizeof * SZ.v i })
  requires struct_V_pts_to a p n xs
  returns  r: U32.t
  ensures  struct_V_pts_to a p n xs
  ensures  pure (r == Seq.index xs (SZ.v i))
{
  unfold struct_V_pts_to a p n xs;
  array_focus uint32_t_repr (a +! struct_V_offsetof_data) uint32_t_sizeof i off;
  uint32_t_of_elem ((a +! struct_V_offsetof_data) +! off);
  let r = uint32_t_read ((a +! struct_V_offsetof_data) +! off);
  uint32_t_to_elem ((a +! struct_V_offsetof_data) +! off);

  array_singleton_intro uint32_t_repr ((a +! struct_V_offsetof_data) +! off)
                        uint32_t_sizeof;
  array_join uint32_t_repr ((a +! struct_V_offsetof_data) +! off) uint32_t_sizeof
             uint32_t_sizeof;
  array_join uint32_t_repr (a +! struct_V_offsetof_data) uint32_t_sizeof off;
  Seq.lemma_eq_intro
    (Seq.append (Seq.slice xs 0 (SZ.v i))
                (Seq.append (Seq.create 1 (Seq.index xs (SZ.v i)))
                            (Seq.slice xs (SZ.v i + 1) (Seq.length xs))))
    xs;
  fold struct_V_pts_to a p n xs;
  r
}
#pop-options
