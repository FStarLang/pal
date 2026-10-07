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
open Pulse.Lib.C.Palow.Index

module ET = Pulse.Lib.C.Palow.Etype
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

let struct_S_ctype : ET.ctype =
  ET.TStruct "S" 8 [(0, uint32_t_ctype); (4, uint8_t_ctype)]

(* The effective-type side condition a struct predicate carries: each field's
   slice of the index admits a read at that field's type. Like `elems_ok` for
   arrays it is stated *pointwise*, so it splits and joins by construction --
   which is what lets `struct_S_split` and `struct_S_join` stay provable. The
   padding bytes are deliberately unconstrained: nothing reads them. *)
let struct_S_fields_ok (e: ET.etypes) : prop =
  ET.elen e == SZ.v struct_S_sizeof /\
  ET.read_ok (Seq.slice e 0 4) uint32_t_ctype /\
  ET.read_ok (Seq.slice e 4 5) uint8_t_ctype

(* The join side: a field slice of the concatenated index is the field's own
   index back. Pure, and the only reason `struct_S_join` goes through. *)
let struct_S_fields_ok_intro (ef eg epad: ET.etypes)
  : Lemma (requires ET.elen ef == 4 /\ ET.elen eg == 1 /\ ET.elen epad == 3
                    /\ ET.read_ok ef uint32_t_ctype /\ ET.read_ok eg uint8_t_ctype)
          (ensures  struct_S_fields_ok (Seq.append ef (Seq.append eg epad)))
  = let e = Seq.append ef (Seq.append eg epad) in
    Seq.lemma_eq_intro (Seq.slice e 0 4) ef;
    Seq.lemma_eq_intro (Seq.slice e 4 5) eg

let struct_S_pts_to ([@@@mkey] a: ptr) (p: perm) (x: struct_S) : slprop =
  exists* b e. mem_pts_to_at a p b e
            ** pure (struct_S_repr x b /\ aligned a struct_S_alignof
                     /\ struct_S_fields_ok e)

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

(* Each field's alignment follows from the structure's plus its offset: clang
   lays a field out at a multiple of its own alignment, so the side condition
   is a fact about the layout and, since both are numerals, a computation. This
   is the whole of what the alignment discipline costs an aggregate. *)
let struct_S_field_aligned (a: ptr)
  : Lemma (requires aligned a struct_S_alignof)
          (ensures  aligned a uint32_t_alignof
                    /\ aligned (a +! struct_S_offsetof_g) uint8_t_alignof)
  = ()

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
  with b e. assert (mem_pts_to_at a p b e
                    ** pure (struct_S_repr x b /\ struct_S_fields_ok e));
  struct_S_repr_elim x b;
  struct_S_field_aligned a;

  mem_split_at a 4sz;
  Seq.lemma_eq_intro (slice b 0 4) (encode 4 None (U32.v x.f));
  uint32_t_conceal a #p #_ #_ #x.f;

  mem_split_at (a +! 4sz) 1sz;
  Seq.slice_slice b 4 8 0 1;
  Seq.slice_slice e 4 8 0 1;
  Seq.lemma_eq_intro (slice (slice b 4 (len b)) 0 1) (encode 1 None (U8.v x.g));
  uint8_t_conceal (a +! struct_S_offsetof_g) #p #_ #_ #x.g;

  Seq.slice_slice b 4 8 1 4;
  Seq.slice_slice e 4 8 1 4;
  mem_hide_etypes ((a +! 4sz) +! 1sz);
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
  with ef. assert (mem_pts_to_at a p (encode 4 None (U32.v x.f)) ef);
  uint8_t_reveal (a +! struct_S_offsetof_g) #p #x.g;
  with eg. assert (mem_pts_to_at (a +! struct_S_offsetof_g) p
                                 (encode 1 None (U8.v x.g)) eg);
  unfold struct_S_padding a p;
  with pad. assert (mem_pts_to (a +! struct_S_padoff) p pad);
  mem_show_etypes (a +! struct_S_padoff);
  with epad. assert (mem_pts_to_at (a +! struct_S_padoff) p pad epad);

  struct_S_padptr a;
  rewrite (mem_pts_to_at (a +! struct_S_padoff) p pad epad)
       as (mem_pts_to_at ((a +! 4sz) +! 1sz) p pad epad);
  rewrite (mem_pts_to_at (a +! struct_S_offsetof_g) p (encode 1 None (U8.v x.g)) eg)
       as (mem_pts_to_at (a +! 4sz) p (encode 1 None (U8.v x.g)) eg);

  mem_join_at (a +! 4sz) #p #(encode 1 None (U8.v x.g)) #pad #eg #epad 1sz;
  mem_join_at a #p #(encode 4 None (U32.v x.f)) #(append (encode 1 None (U8.v x.g)) pad)
                 #ef #(Seq.append eg epad) 4sz;

  struct_S_repr_intro x (encode 4 None (U32.v x.f)) (encode 1 None (U8.v x.g)) pad;
  struct_S_fields_ok_intro ef eg epad;
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

let struct_T_ctype : ET.ctype =
  ET.TStruct "T" 8 [(0, uint32_t_ctype); (4, uint32_t_ctype)]

let struct_T_fields_ok (e: ET.etypes) : prop =
  ET.elen e == SZ.v struct_T_sizeof /\
  ET.read_ok (Seq.slice e 0 4) uint32_t_ctype /\
  ET.read_ok (Seq.slice e 4 8) uint32_t_ctype

let struct_T_fields_ok_intro (ey ez: ET.etypes)
  : Lemma (requires ET.elen ey == 4 /\ ET.elen ez == 4
                    /\ ET.read_ok ey uint32_t_ctype /\ ET.read_ok ez uint32_t_ctype)
          (ensures  struct_T_fields_ok (Seq.append ey ez))
  = let e = Seq.append ey ez in
    Seq.lemma_eq_intro (Seq.slice e 0 4) ey;
    Seq.lemma_eq_intro (Seq.slice e 4 8) ez

let struct_T_pts_to ([@@@mkey] a: ptr) (p: perm) (x: struct_T) : slprop =
  exists* b e. mem_pts_to_at a p b e
            ** pure (struct_T_repr x b /\ aligned a struct_T_alignof
                     /\ struct_T_fields_ok e)

let struct_T_field_aligned (a: ptr)
  : Lemma (requires aligned a struct_T_alignof)
          (ensures  aligned a uint32_t_alignof
                    /\ aligned (a +! struct_T_offsetof_z) uint32_t_alignof)
  = aligned_field a struct_T_alignof struct_T_offsetof_y uint32_t_alignof;
    aligned_field a struct_T_alignof struct_T_offsetof_z uint32_t_alignof

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
  struct_T_field_aligned a;
  with b e. assert (mem_pts_to_at a p b e
                    ** pure (struct_T_repr x b /\ struct_T_fields_ok e));
  mem_split_at a 4sz;
  Seq.lemma_eq_intro (slice b 0 4) (encode 4 None (U32.v x.y));
  Seq.lemma_eq_intro (slice b 4 (len b)) (encode 4 None (U32.v x.z));
  Seq.lemma_eq_intro (Seq.slice e 4 (ET.elen e)) (Seq.slice e 4 8);
  uint32_t_conceal a #p #_ #_ #x.y;
  uint32_t_conceal (a +! struct_T_offsetof_z) #p #_ #_ #x.z;
}

ghost fn struct_T_join (a: ptr) (#p: perm) (#x: struct_T)
  requires uint32_t_pts_to a p x.y
  requires uint32_t_pts_to (a +! struct_T_offsetof_z) p x.z
  ensures  struct_T_pts_to a p x
{
  uint32_t_reveal a #p #x.y;
  with ey. assert (mem_pts_to_at a p (encode 4 None (U32.v x.y)) ey);
  uint32_t_reveal (a +! struct_T_offsetof_z) #p #x.z;
  with ez. assert (mem_pts_to_at (a +! struct_T_offsetof_z) p
                                 (encode 4 None (U32.v x.z)) ez);
  rewrite (mem_pts_to_at (a +! struct_T_offsetof_z) p (encode 4 None (U32.v x.z)) ez)
       as (mem_pts_to_at (a +! 4sz) p (encode 4 None (U32.v x.z)) ez);
  mem_join_at a #p #(encode 4 None (U32.v x.y)) #(encode 4 None (U32.v x.z)) #ey #ez 4sz;
  struct_T_repr_intro x (encode 4 None (U32.v x.y)) (encode 4 None (U32.v x.z));
  struct_T_fields_ok_intro ey ez;
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
  ** array_pts_to uint32_t_repr uint32_t_ctype (SZ.v uint32_t_sizeof) (SZ.v uint32_t_alignof)
                    (a +! struct_V_offsetof_data) p xs
  ** pure (U32.v n == Seq.length xs)

(* Bridging the generic element view and the scalar points-to. `uint32_t_repr x b`
   is by definition `b == encode 4 None (U32.v x)`, so both directions are a
   fold/unfold pair; PAL emits one such pair per scalar type. *)
ghost fn uint32_t_of_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to uint32_t_repr uint32_t_ctype a p x
  requires pure (aligned a uint32_t_alignof)
  ensures  uint32_t_pts_to a p x
{
  unfold elem_pts_to uint32_t_repr uint32_t_ctype a p x;
  uint32_t_conceal a #p #_ #_ #x;
}

ghost fn uint32_t_to_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  elem_pts_to uint32_t_repr uint32_t_ctype a p x
  ensures  pure (aligned a uint32_t_alignof)
{
  uint32_t_reveal a #p #x;
  fold elem_pts_to uint32_t_repr uint32_t_ctype a p x;
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
  array_focus uint32_t_repr uint32_t_ctype (a +! struct_V_offsetof_data) uint32_t_sizeof uint32_t_alignof i off;
  uint32_t_of_elem ((a +! struct_V_offsetof_data) +! off);
  let r = uint32_t_read ((a +! struct_V_offsetof_data) +! off);
  uint32_t_to_elem ((a +! struct_V_offsetof_data) +! off);

  array_singleton_intro uint32_t_repr uint32_t_ctype ((a +! struct_V_offsetof_data) +! off)
                        uint32_t_sizeof uint32_t_alignof;
  array_join uint32_t_repr uint32_t_ctype ((a +! struct_V_offsetof_data) +! off) uint32_t_sizeof
             uint32_t_alignof uint32_t_sizeof;
  array_join uint32_t_repr uint32_t_ctype (a +! struct_V_offsetof_data) uint32_t_sizeof
             uint32_t_alignof off;
  Seq.lemma_eq_intro
    (Seq.append (Seq.slice xs 0 (SZ.v i))
                (Seq.append (Seq.create 1 (Seq.index xs (SZ.v i)))
                            (Seq.slice xs (SZ.v i + 1) (Seq.length xs))))
    xs;
  fold struct_V_pts_to a p n xs;
  r
}
#pop-options
