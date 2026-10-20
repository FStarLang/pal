module Pulse.Lib.C.Palow.Effective.Retained.Array

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module A = Pulse.Lib.C.Palow.Array
module ET = Pulse.Lib.C.Palow.Etype
module Rel = Pulse.Lib.C.Palow.Effective.Relation
module R = Pulse.Lib.C.Palow.Effective.Retained
module V = Pulse.Lib.C.Palow.Effective.Value
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas

let scalar_element (ct: ET.ctype) : prop =
  match ct with
  | ET.TScalar _ -> True
  | _ -> False

(* These retained owners support scalar elements only; aggregate structural
   views do not justify their nominal scalar ownership bridges.
   A dynamic array is a sequence of element views, not a newly established
   nominal TArr. Retention is elementwise so a subarray may keep preexisting
   enclosing labels, while fresh labels cannot invent a foreign parent.
   Installing a new whole-array label requires a separate explicit effect,
   not the default contract of an ordinary elementwise array call. *)
let retains (ct: ET.ctype) (esize n: nat) (base actual: ET.etypes) : prop =
  esize == ET.csize ct /\ ET.elen base == esize * n /\
  ET.elen actual == ET.elen base /\
  (forall (i: nat). i < n ==>
    Rel.retains (A.elem_etypes esize base i) (A.elem_etypes esize actual i) ct)

let retains_refl (ct: ET.ctype) (esize n: nat) (e: ET.etypes)
  : Lemma (requires A.array_read_ok ct esize n e)
          (ensures retains ct esize n e e) = ()

let retains_trans (ct: ET.ctype) (esize n: nat) (base middle actual: ET.etypes)
  : Lemma (requires retains ct esize n base middle /\ retains ct esize n middle actual)
          (ensures retains ct esize n base actual)
  = let aux (i: nat { i < n })
      : Lemma (Rel.retains (A.elem_etypes esize base i)
                          (A.elem_etypes esize actual i) ct)
      = Rel.retains_trans (A.elem_etypes esize base i)
                          (A.elem_etypes esize middle i)
                          (A.elem_etypes esize actual i) ct
    in Classical.forall_intro aux

#push-options "--z3rlimit 40"
let retains_split (ct: ET.ctype) (esize n: nat) (base actual: ET.etypes)
    (k: nat { k <= n /\ esize * k <= ET.elen base /\ esize * k <= ET.elen actual })
  : Lemma (requires retains ct esize n base actual)
          (ensures
            retains ct esize k
              (Seq.slice base 0 (esize * k)) (Seq.slice actual 0 (esize * k)) /\
            retains ct esize (n - k)
              (Seq.slice base (esize * k) (ET.elen base))
              (Seq.slice actual (esize * k) (ET.elen actual)))
  = Math.distributivity_sub_right esize n k;
    let pre (i: nat) : Lemma (i < k ==>
      Rel.retains (A.elem_etypes esize (Seq.slice base 0 (esize * k)) i)
                  (A.elem_etypes esize (Seq.slice actual 0 (esize * k)) i) ct) =
      if i < k then begin
        A.elem_fits esize k i;
        Seq.slice_slice base 0 (esize * k) (esize * i) (esize * i + esize);
        Seq.slice_slice actual 0 (esize * k) (esize * i) (esize * i + esize)
      end
    in
    Classical.forall_intro pre;
    let post (i: nat) : Lemma (i < n - k ==>
      Rel.retains
        (A.elem_etypes esize (Seq.slice base (esize * k) (ET.elen base)) i)
        (A.elem_etypes esize (Seq.slice actual (esize * k) (ET.elen actual)) i) ct) =
      if i < n - k then begin
        A.elem_fits esize (n - k) i;
        A.elem_fits esize n (k + i);
        Math.distributivity_sub_right esize n k;
        Math.distributivity_add_right esize k i;
        Seq.slice_slice base (esize * k) (ET.elen base)
          (esize * i) (esize * i + esize);
        Seq.slice_slice actual (esize * k) (ET.elen actual)
          (esize * i) (esize * i + esize)
      end
    in Classical.forall_intro post

let retains_join (ct: ET.ctype) (esize n m: nat)
    (b1 a1 b2 a2: ET.etypes)
  : Lemma (requires retains ct esize n b1 a1 /\ retains ct esize m b2 a2)
          (ensures retains ct esize (n + m) (Seq.append b1 b2) (Seq.append a1 a2))
  = Math.distributivity_add_right esize n m;
    let base = Seq.append b1 b2 in
    let actual = Seq.append a1 a2 in
    let aux (i: nat) : Lemma (i < n + m ==>
      Rel.retains (A.elem_etypes esize base i) (A.elem_etypes esize actual i) ct) =
      if i < n then begin
        A.elem_fits esize n i;
        Seq.lemma_eq_intro (Seq.slice base 0 (ET.elen b1)) b1;
        Seq.lemma_eq_intro (Seq.slice actual 0 (ET.elen a1)) a1;
        Seq.slice_slice base 0 (ET.elen b1) (esize * i) (esize * i + esize);
        Seq.slice_slice actual 0 (ET.elen a1) (esize * i) (esize * i + esize)
      end else if i < n + m then begin
        let j = i - n in
        A.elem_fits esize m j;
        Math.distributivity_add_right esize n j;
        Seq.lemma_eq_intro (Seq.slice base (ET.elen b1) (ET.elen base)) b2;
        Seq.lemma_eq_intro (Seq.slice actual (ET.elen a1) (ET.elen actual)) a2;
        Seq.slice_slice base (ET.elen b1) (ET.elen base)
          (esize * j) (esize * j + esize);
        Seq.slice_slice actual (ET.elen a1) (ET.elen actual)
          (esize * j) (esize * j + esize)
      end
    in Classical.forall_intro aux
#pop-options

let value (#t: Type) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (esize alignment: nat) (base: ET.etypes)
    ([@@@mkey] a: ptr) (p: perm) (xs: Seq.seq t) : slprop =
  exists* actual. A.array_pts_to_at ct repr esize alignment a p xs actual
    ** pure (scalar_element ct /\
             A.array_read_ok ct esize (Seq.length xs) base /\
             retains ct esize (Seq.length xs) base actual)

let storage (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (esize alignment n: nat) (base: ET.etypes) ([@@@mkey] a: ptr) : slprop =
  exists* xs. value ct (A.maybe_repr repr esize) esize alignment base a 1.0R xs
    ** pure (Seq.length xs == n)

ghost fn retain (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t)
  requires A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a p xs
  requires pure (scalar_element ct)
  ensures exists* base. value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
{
  unfold A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a p xs;
  with b e. assert (mem_pts_to_at a p b e);
  retains_refl ct (SZ.v esize) (Seq.length xs) e;
  A.array_conceal_at ct repr a esize alignment #p #b #xs #e;
  fold value ct repr (SZ.v esize) (SZ.v alignment) e a p xs;
}

ghost fn release (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a p xs
{
  unfold value ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
  A.array_reveal_at ct repr a esize alignment;
  fold A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a p xs;
}

ghost fn reveal (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures exists* b actual. mem_pts_to_at a p b actual
    ** pure (scalar_element ct /\
             A.array_repr repr (SZ.v esize) xs b /\
             A.array_aligned (SZ.v esize) (SZ.v alignment) a /\
             A.array_read_ok ct (SZ.v esize) (Seq.length xs) base /\
             A.array_read_ok ct (SZ.v esize) (Seq.length xs) actual /\
             retains ct (SZ.v esize) (Seq.length xs) base actual)
{
  unfold value ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
  A.array_reveal_at ct repr a esize alignment;
}

ghost fn conceal (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t)
    (#p: perm) (#xs: Seq.seq t) (#base #actual: ET.etypes)
  requires A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) a p xs actual
  requires pure (scalar_element ct)
  requires pure (retains ct (SZ.v esize) (Seq.length xs) base actual)
  requires pure (A.array_read_ok ct (SZ.v esize) (Seq.length xs) base)
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
{
  fold value ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
}

ghost fn properties (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  preserves value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures pure (scalar_element ct /\
                A.array_read_ok ct (SZ.v esize) (Seq.length xs) base /\
                A.array_aligned (SZ.v esize) (SZ.v alignment) a)
{
  reveal ct repr a esize alignment;
  with b actual. assert (mem_pts_to_at a p b actual);
  A.array_conceal_at ct repr a esize alignment #p #b #xs #actual;
  conceal ct repr a esize alignment #p #xs #base #actual;
}

(* A retained fraction pins the actual index across a public read-only call. *)
ghost fn borrow_public_read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                            (a: ptr) (esize alignment: SZ.t)
                            (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a (p /. 2.0R) xs
       ** A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a (p /. 2.0R) xs
{
  reveal ct repr a esize alignment #p #xs #base;
  with b actual. assert (mem_pts_to_at a p b actual);
  mem_share_at a #p #b #actual;
  A.array_conceal_at ct repr a esize alignment #(p /. 2.0R) #b #xs #actual;
  conceal ct repr a esize alignment #(p /. 2.0R) #xs #base #actual;
  fold A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a (p /. 2.0R) xs;
}

ghost fn restore_public_read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                             (a: ptr) (esize alignment: SZ.t)
                             (#p1 #p2: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p1 xs
  requires A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a p2 xs
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a (p1 +. p2) xs
{
  reveal ct repr a esize alignment #p1 #xs #base;
  with b1 actual. assert (mem_pts_to_at a p1 b1 actual);
  unfold A.array_pts_to ct repr (SZ.v esize) (SZ.v alignment) a p2 xs;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_gather_at a #p1 #p2 #b1 #b2 #actual #e2;
  A.array_conceal_at ct repr a esize alignment #(p1 +. p2) #b1 #xs #actual;
  conceal ct repr a esize alignment #(p1 +. p2) #xs #base #actual;
}

ghost fn offset_fits (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
    (i: SZ.t { SZ.v i < Seq.length xs })
  preserves value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures pure (SZ.fits (SZ.v esize * SZ.v i) /\
                SZ.v esize * SZ.v i + SZ.v esize <= ET.elen base)
{
  reveal ct repr a esize alignment;
  with b actual. assert (mem_pts_to_at a p b actual);
  mem_pts_to_at_fits a;
  A.elem_fits (SZ.v esize) (Seq.length xs) (SZ.v i);
  SZ.fits_lte (SZ.v esize * SZ.v i) (addr_of a + len b);
  A.array_conceal_at ct repr a esize alignment #p #b #xs #actual;
  conceal ct repr a esize alignment #p #xs #base #actual;
}

ghost fn split (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t)
    (#base: ET.etypes { ET.elen base == SZ.v esize * Seq.length xs })
    (n: SZ.t { SZ.v n <= Seq.length xs })
    (off: SZ.t { SZ.v off == SZ.v esize * SZ.v n /\ SZ.v off <= ET.elen base })
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base 0 (SZ.v off)) a p (Seq.slice xs 0 (SZ.v n))
  ensures value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base (SZ.v off) (ET.elen base)) (a +! off) p
    (Seq.slice xs (SZ.v n) (Seq.length xs))
  ensures pure (A.array_aligned (SZ.v esize) (SZ.v alignment) (a +! off))
  ensures pure (SZ.v esize == ET.csize ct)
{
  unfold value ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
  with actual. assert (A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) a p xs actual);
  A.array_read_ok_split ct (SZ.v esize) (Seq.length xs) base (SZ.v n);
  retains_split ct (SZ.v esize) (Seq.length xs) base actual (SZ.v n);
  A.array_split_at ct repr a esize alignment #p #xs #actual n off;
  fold value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base 0 (SZ.v off)) a p (Seq.slice xs 0 (SZ.v n));
  fold value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base (SZ.v off) (ET.elen base)) (a +! off) p
    (Seq.slice xs (SZ.v n) (Seq.length xs));
}

ghost fn join (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (off: SZ.t)
    (#p: perm) (#xs #ys: Seq.seq t) (#base1 #base2: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base1 a p xs
  requires value ct repr (SZ.v esize) (SZ.v alignment) base2 (a +! off) p ys
  requires pure (SZ.v off == SZ.v esize * Seq.length xs)
  ensures value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.append base1 base2) a p (Seq.append xs ys)
{
  unfold value ct repr (SZ.v esize) (SZ.v alignment) base1 a p xs;
  with e1. assert (A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) a p xs e1);
  unfold value ct repr (SZ.v esize) (SZ.v alignment) base2 (a +! off) p ys;
  with e2. assert (A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) (a +! off) p ys e2);
  A.array_read_ok_join ct (SZ.v esize) (Seq.length xs) (Seq.length ys) base1 base2;
  retains_join ct (SZ.v esize) (Seq.length xs) (Seq.length ys) base1 e1 base2 e2;
  A.array_join_at ct repr a esize alignment off #p #xs #ys #e1 #e2;
  fold value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.append base1 base2) a p (Seq.append xs ys);
}

ghost fn singleton_elim (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#x: t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p (Seq.create 1 x)
  ensures R.value ct repr alignment a p x base
{
  unfold value ct repr (SZ.v esize) (SZ.v alignment) base a p (Seq.create 1 x);
  with e. assert (A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) a p (Seq.create 1 x) e);
  A.array_reveal_at ct repr a esize alignment;
  with b. assert (mem_pts_to_at a p b e);
  A.singleton_repr_elim repr (SZ.v esize) x b;
  Seq.lemma_eq_intro (Seq.slice base 0 (ET.elen base)) base;
  Seq.lemma_eq_intro (Seq.slice e 0 (ET.elen e)) e;
  V.claim ct repr alignment a #p #x #b #e;
  R.conceal ct repr alignment a #p #x #e #base;
}

ghost fn singleton_intro (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#x: t) (#base: ET.etypes)
  requires R.value ct repr alignment a p x base
  requires pure (scalar_element ct)
  requires pure (SZ.v esize == ET.csize ct /\
                 A.array_aligned (SZ.v esize) (SZ.v alignment) a)
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a p (Seq.create 1 x)
{
  R.reveal_value ct repr alignment a;
  with b e. assert (mem_pts_to_at a p b e);
  A.singleton_repr repr (SZ.v esize) x b;
  Seq.lemma_eq_intro (Seq.slice base 0 (ET.elen base)) base;
  Seq.lemma_eq_intro (Seq.slice e 0 (ET.elen e)) e;
  A.array_conceal_at ct repr a esize alignment #p #b #(Seq.create 1 x) #e;
  fold value ct repr (SZ.v esize) (SZ.v alignment) base a p (Seq.create 1 x);
}

ghost fn focus (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t)
    (#base: ET.etypes { ET.elen base == SZ.v esize * Seq.length xs })
    (i: SZ.t { SZ.v i < Seq.length xs })
    (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i /\
                SZ.v off + SZ.v esize <= ET.elen base })
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base 0 (SZ.v off)) a p (Seq.slice xs 0 (SZ.v i))
  ensures R.value ct repr alignment (a +! off) p (Seq.index xs (SZ.v i))
    (Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize))
  ensures value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base (SZ.v off + SZ.v esize) (ET.elen base))
    ((a +! off) +! esize) p (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  ensures pure (A.array_aligned (SZ.v esize) (SZ.v alignment) (a +! off))
  ensures pure (SZ.v esize == ET.csize ct)
{
  split ct repr a esize alignment #p #xs #base i off;
  let tail = Seq.slice xs (SZ.v i) (Seq.length xs);
  let tailbase = Seq.slice base (SZ.v off) (ET.elen base);
  split ct repr (a +! off) esize alignment #p #tail #tailbase 1sz esize;
  Seq.lemma_eq_intro (Seq.slice tail 0 1) (Seq.create 1 (Seq.index xs (SZ.v i)));
  Seq.lemma_eq_intro (Seq.slice tail 1 (Seq.length tail))
                    (Seq.slice xs (SZ.v i + 1) (Seq.length xs));
  Seq.slice_slice base (SZ.v off) (ET.elen base) 0 (SZ.v esize);
  Seq.slice_slice base (SZ.v off) (ET.elen base) (SZ.v esize) (ET.elen tailbase);
  singleton_elim ct repr (a +! off) esize alignment #p
    #(Seq.index xs (SZ.v i)) #(Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize));
}

ghost fn unfocus (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#xs: Seq.seq t) (#y: t)
    (#base: ET.etypes { ET.elen base == SZ.v esize * Seq.length xs })
    (i: SZ.t { SZ.v i < Seq.length xs })
    (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i /\
                SZ.v off + SZ.v esize <= ET.elen base })
  requires value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base 0 (SZ.v off)) a p (Seq.slice xs 0 (SZ.v i))
  requires R.value ct repr alignment (a +! off) p y
    (Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize))
  requires value ct repr (SZ.v esize) (SZ.v alignment)
    (Seq.slice base (SZ.v off + SZ.v esize) (ET.elen base))
    ((a +! off) +! esize) p (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  requires pure (SZ.v esize == ET.csize ct /\
                 A.array_aligned (SZ.v esize) (SZ.v alignment) (a +! off))
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a p (Seq.upd xs (SZ.v i) y)
{
  properties ct repr a esize alignment
    #p #(Seq.slice xs 0 (SZ.v i)) #(Seq.slice base 0 (SZ.v off));
  singleton_intro ct repr (a +! off) esize alignment #p #y
    #(Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize));
  join ct repr (a +! off) esize alignment esize
    #p #(Seq.create 1 y) #(Seq.slice xs (SZ.v i + 1) (Seq.length xs))
    #(Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize))
    #(Seq.slice base (SZ.v off + SZ.v esize) (ET.elen base));
  join ct repr a esize alignment off
    #p #(Seq.slice xs 0 (SZ.v i))
    #(Seq.append (Seq.create 1 y) (Seq.slice xs (SZ.v i + 1) (Seq.length xs)))
    #(Seq.slice base 0 (SZ.v off))
    #(Seq.append (Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize))
                 (Seq.slice base (SZ.v off + SZ.v esize) (ET.elen base)));
  Seq.lemma_eq_intro
    (Seq.append (Seq.slice base 0 (SZ.v off))
      (Seq.append (Seq.slice base (SZ.v off) (SZ.v off + SZ.v esize))
                  (Seq.slice base (SZ.v off + SZ.v esize) (ET.elen base)))) base;
  A.upd_split xs (SZ.v i) y;
  rewrite (value ct repr (SZ.v esize) (SZ.v alignment) base a p
    (Seq.append (Seq.slice xs 0 (SZ.v i))
      (Seq.append (Seq.create 1 y) (Seq.slice xs (SZ.v i + 1) (Seq.length xs)))))
    as (value ct repr (SZ.v esize) (SZ.v alignment) base a p
      (Seq.upd xs (SZ.v i) y));
}

ghost fn forget (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R xs
  ensures value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a 1.0R (A.somes xs)
{
  reveal ct repr a esize alignment;
  with b actual. assert (mem_pts_to_at a 1.0R b actual);
  A.array_conceal_at ct (A.maybe_repr repr (SZ.v esize)) a esize alignment
    #1.0R #b #(A.somes xs) #actual;
  fold value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a 1.0R (A.somes xs);
}

ghost fn forget_all (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R xs
  ensures storage ct repr (SZ.v esize) (SZ.v alignment) (Seq.length xs) base a
{
  forget ct repr a esize alignment;
  fold storage ct repr (SZ.v esize) (SZ.v alignment) (Seq.length xs) base a;
}

ghost fn claim_all (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (vs: Seq.seq t)
    (#xs: Seq.seq (option t) { Seq.length xs == Seq.length vs }) (#base: ET.etypes)
  requires value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a 1.0R xs
  requires pure (forall (i: nat). i < Seq.length vs ==>
    Seq.index xs i == Some (Seq.index vs i))
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R vs
{
  reveal ct (A.maybe_repr repr (SZ.v esize)) a esize alignment;
  with b actual. assert (mem_pts_to_at a 1.0R b actual);
  A.array_conceal_at ct repr a esize alignment #1.0R #b #vs #actual;
  conceal ct repr a esize alignment #1.0R #vs #base #actual;
}

ghost fn claim_all_somes (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#xs: Seq.seq (option t)) (#base: ET.etypes)
  requires value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a 1.0R xs
  requires pure (A.all_some xs)
  ensures exists* vs. value ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R vs
    ** pure (Seq.length vs == Seq.length xs)
{
  claim_all ct repr a esize alignment (A.unsomes xs) #xs #base;
}

ghost fn somes (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm)
    (#xs: Seq.seq (option t)) (#base: ET.etypes)
  requires value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a p xs
  requires pure (A.all_some xs \/ (SZ.v esize > 0 /\ A.all_some_sz xs))
  ensures exists* vs. value ct repr (SZ.v esize) (SZ.v alignment) base a p vs
    ** pure (xs == A.somes vs /\ Seq.length vs == Seq.length xs /\
             (forall (i: nat). {:pattern Seq.index vs i}
               i < Seq.length vs ==> Seq.index xs i == Some (Seq.index vs i)))
{
  reveal ct (A.maybe_repr repr (SZ.v esize)) a esize alignment;
  with b actual. assert (mem_pts_to_at a p b actual);
  mem_pts_to_at_fits a;
  A.length_fits (SZ.v esize) (Seq.length xs) (addr_of a + len b);
  Classical.move_requires A.all_some_of_sz xs;
  let vs = A.unsomes xs;
  Seq.lemma_eq_intro xs (A.somes vs);
  A.array_conceal_at ct repr a esize alignment #p #b #vs #actual;
  conceal ct repr a esize alignment #p #vs #base #actual;
}

ghost fn unsomes (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#vs: Seq.seq t) (#base: ET.etypes)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a p vs
  ensures value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a p (A.somes vs)
{
  reveal ct repr a esize alignment;
  with b actual. assert (mem_pts_to_at a p b actual);
  A.array_conceal_at ct (A.maybe_repr repr (SZ.v esize)) a esize alignment
    #p #b #(A.somes vs) #actual;
  conceal ct (A.maybe_repr repr (SZ.v esize)) a esize alignment
    #p #(A.somes vs) #base #actual;
}

ghost fn retain_storage (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment n: SZ.t)
  requires A.array_pts_to_uninit ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) a
  requires pure (scalar_element ct)
  ensures exists* base. storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a
{
  unfold A.array_pts_to_uninit ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) a;
  with xs. assert (A.array_pts_to ct (A.maybe_repr repr (SZ.v esize))
    (SZ.v esize) (SZ.v alignment) a 1.0R xs);
  retain ct (A.maybe_repr repr (SZ.v esize)) a esize alignment;
  with base. assert (value ct (A.maybe_repr repr (SZ.v esize))
    (SZ.v esize) (SZ.v alignment) base a 1.0R xs);
  fold storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a;
}

ghost fn release_storage (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment n: SZ.t) (#base: ET.etypes)
  requires storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a
  ensures A.array_pts_to_uninit ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) a
{
  unfold storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a;
  release ct (A.maybe_repr repr (SZ.v esize)) a esize alignment;
  fold A.array_pts_to_uninit ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) a;
}

ghost fn element_storage (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#x: option t) (#base: ET.etypes)
  requires R.value ct (A.maybe_repr repr (SZ.v esize)) alignment a 1.0R x base
  ensures R.storage ct alignment a base
{
  R.reveal_value ct (A.maybe_repr repr (SZ.v esize)) alignment a;
  V.claim_storage ct alignment a;
  fold R.storage ct alignment a base;
}

ghost fn element_some (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (#p: perm) (#x: t) (#base: ET.etypes)
  requires R.value ct repr alignment a p x base
  ensures R.value ct (A.maybe_repr repr (SZ.v esize)) alignment a p (Some x) base
{
  R.reveal_value ct repr alignment a;
  with b actual. assert (mem_pts_to_at a p b actual);
  V.claim ct (A.maybe_repr repr (SZ.v esize)) alignment a #p #(Some x) #b #actual;
  R.conceal ct (A.maybe_repr repr (SZ.v esize)) alignment a #p #(Some x) #actual #base;
}

ghost fn element_get (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t)
    (#p: perm) (#x: option t { Some? x }) (#base: ET.etypes)
  requires R.value ct (A.maybe_repr repr (SZ.v esize)) alignment a p x base
  ensures R.value ct repr alignment a p (Some?.v x) base
{
  R.reveal_value ct (A.maybe_repr repr (SZ.v esize)) alignment a;
  with b actual. assert (mem_pts_to_at a p b actual);
  V.claim ct repr alignment a #p #(Some?.v x) #b #actual;
  R.conceal ct repr alignment a #p #(Some?.v x) #actual #base;
}

fn read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (load: R.indexed_reader t ct repr alignment)
    (#p: perm) (#xs: Seq.seq t)
    (#base: ET.etypes { ET.elen base == SZ.v esize * Seq.length xs })
    (i: SZ.t { SZ.v i < Seq.length xs })
    (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i /\
                SZ.v off + SZ.v esize <= ET.elen base })
  preserves value ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  returns y: t
  ensures pure (y == Seq.index xs (SZ.v i))
{
  focus ct repr a esize alignment #p #xs #base i off;
  let y = R.read_retained ct repr alignment load (a +! off);
  unfocus ct repr a esize alignment #p #xs #(Seq.index xs (SZ.v i)) #base i off;
  Seq.lemma_eq_intro (Seq.upd xs (SZ.v i) (Seq.index xs (SZ.v i))) xs;
  rewrite (value ct repr (SZ.v esize) (SZ.v alignment) base a p
    (Seq.upd xs (SZ.v i) (Seq.index xs (SZ.v i))))
    as (value ct repr (SZ.v esize) (SZ.v alignment) base a p xs);
  y
}

fn write (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (store: R.indexed_writer t ct repr alignment)
    (#xs: Seq.seq t) (#base: ET.etypes { ET.elen base == SZ.v esize * Seq.length xs })
    (i: SZ.t { SZ.v i < Seq.length xs })
    (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i /\
                SZ.v off + SZ.v esize <= ET.elen base }) (y: t)
  requires value ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R xs
  ensures value ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R
    (Seq.upd xs (SZ.v i) y)
{
  focus ct repr a esize alignment #1.0R #xs #base i off;
  R.write_retained ct repr alignment store (a +! off) y;
  unfocus ct repr a esize alignment #1.0R #xs #y #base i off;
}

fn write_uninit (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t) (store: R.indexed_writer t ct repr alignment)
    (#xs: Seq.seq (option t)) (#base: ET.etypes { ET.elen base == SZ.v esize * Seq.length xs })
    (i: SZ.t { SZ.v i < Seq.length xs })
    (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i /\
                SZ.v off + SZ.v esize <= ET.elen base }) (y: t)
  requires value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a 1.0R xs
  ensures value ct (A.maybe_repr repr (SZ.v esize)) (SZ.v esize) (SZ.v alignment)
    base a 1.0R (Seq.upd xs (SZ.v i) (Some y))
{
  focus ct (A.maybe_repr repr (SZ.v esize)) a esize alignment #1.0R #xs #base i off;
  element_storage ct repr (a +! off) esize alignment;
  R.write_uninit_retained ct repr alignment store (a +! off) y;
  element_some ct repr (a +! off) esize alignment;
  unfocus ct (A.maybe_repr repr (SZ.v esize)) a esize alignment
    #1.0R #xs #(Some y) #base i off;
}

let retains_some_entry (ct: ET.ctype) (esize n: nat) (base actual: ET.etypes)
    (i: nat { i < n })
    (k: nat { k < ET.elen (A.elem_etypes esize base i) })
    (en: ET.etype_entry)
  : Lemma (requires retains ct esize n base actual /\
                    ET.eget (A.elem_etypes esize base i) k == Some en)
          (ensures ET.eget (A.elem_etypes esize actual i) k == Some en)
  = ()

let model_fresh_elements_do_not_establish_array ()
  : Lemma
      (let ct = ET.TScalar ET.SUInt32 in
       let actual = Seq.append (ET.etypes_of ct false) (ET.etypes_of ct false) in
       retains ct 4 2 (ET.etypes_none 8) actual /\
       not (ET.established_type actual (ET.TArr ct 2)))
  = ()

let model_fresh_elements_reject_foreign_parent ()
  : Lemma
      (let ct = ET.TScalar ET.SUInt32 in
       let parent = ET.TStruct "Foreign" 8 [(0, ct); (4, ct)] in
       not (retains ct 4 2 (ET.etypes_none 8) (ET.etypes_of parent false)))
  = ()
