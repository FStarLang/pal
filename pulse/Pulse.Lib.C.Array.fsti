module Pulse.Lib.C.Array
open Pulse
open Pulse.Lib.C.Inhabited
open Pulse.Lib.SmallType
module SZ = FStar.SizeT

#lang-pulse

val array ([@@@unused] a:Type u#a) : Type u#0

val array_null #a : array a
val array_is_null #a (r: array a) : b:bool {b <==> r == array_null}

instance has_zero_default_array (a:Type) : Pulse.Lib.C.Inhabited.has_zero_default (array a) = {
  zero_default = array_null
}

val array_spec (a: Type u#a) : Type u#a

val array_spec_len #a (s: array_spec a) : GTot nat
val array_spec_initd #a (s: array_spec a) (i: nat) : prop
val array_spec_mask #a (s: array_spec a) (i: nat) : prop
val array_spec_idx #a (s: array_spec a) (i: nat { array_spec_initd s i }) : Tot a

// val array_spec_len_fits #a s : Lemma (SZ.fits (array_spec_len #a s)) [SMTPat (array_spec_len #a s)]

let array_spec_full_mask #a (s: array_spec a) =
  forall (i:nat). {:pattern array_spec_mask s i} i < array_spec_len s ==> array_spec_mask s i

let array_spec_initialized #a (s: array_spec a) =
  forall (i:nat). {:pattern array_spec_initd s i} i < array_spec_len s ==> array_spec_initd s i

let array_spec_full #a (s: array_spec a) =
  array_spec_full_mask s /\ array_spec_initialized s

let full_array_spec a = s: array_spec a { array_spec_full s }

val array_spec_ext #a (s1 s2: array_spec a) :
  Lemma (requires
    array_spec_len s1 == array_spec_len s2
      /\ (forall (i:nat). i < array_spec_len s1 ==> (array_spec_initd s1 i <==> array_spec_initd s2 i))
      /\ (forall (i:nat). i < array_spec_len s1 ==> (array_spec_mask s1 i <==> array_spec_mask s2 i))
      /\ (forall (i:nat). i < array_spec_len s1 /\ array_spec_initd s1 i ==> array_spec_idx s1 i == array_spec_idx s2 i))
  (ensures s1 == s2)

val array_spec_zeroed (a: Type) (n: nat) (x: a) : array_spec a
val array_spec_zeroed_len a n x : Lemma (array_spec_len (array_spec_zeroed a n x) == n) [SMTPat (array_spec_len (array_spec_zeroed a n x))]
val array_spec_zeroed_initd a n x (i:nat) : Lemma (i < n ==> array_spec_initd (array_spec_zeroed a n x) i) [SMTPat (array_spec_initd (array_spec_zeroed a n x) i)]
val array_spec_zeroed_mask a n x (i:nat) : Lemma (i < n ==> array_spec_mask (array_spec_zeroed a n x) i) [SMTPat (array_spec_mask (array_spec_zeroed a n x) i)]
val array_spec_zeroed_idx a n x (i:nat) : Lemma (i < n ==> array_spec_idx (array_spec_zeroed a n x) i == x) [SMTPat (array_spec_idx (array_spec_zeroed a n x) i)]

val array_pts_to #a ([@@@mkey] x: array a) (p: perm) (y: array_spec a) : slprop

let array_spec_seq #a (s: array_spec a) : GTot (Seq.seq (option a)) =
  Seq.init_ghost (array_spec_len s) fun i -> if array_spec_initd s i then Some (array_spec_idx s i) else None

let array_spec_of #a (x: array a) #p #y =
  observe (array_pts_to x p) #y

fn array_read_all u#a (#a: Type u#a) (x: array a)
  preserves array_pts_to x 'p 'y
  returns z: array_spec a
  ensures rewrites_to z 'y

ghost fn array_value_of u#a (#a: Type u#a) (x: array a) (#p: perm) (#y: array_spec a)
  preserves array_pts_to x p y
  returns v: Seq.seq (option a)
  ensures rewrites_to v (array_spec_seq y)
{ array_spec_seq y }

[@@pulse_eager_unfold]
let array_pts_to_full (#t: Type u#a) (a: array t) p (y: full_array_spec t) =
  array_pts_to a p y

[@@pulse_eager_unfold]
let array_pts_to_uninit (#t: Type u#a) (a: array t) y =
  array_pts_to a 1.0R y ** with_pure (array_spec_full_mask y) fun _ -> emp

[@@pulse_eager_unfold]
let array_pts_to_uninit' (#t: Type u#a) (a: array t) =
  exists* y. array_pts_to_uninit a y

val freeable_array (#a:Type) (r:array a) : slprop

val array_spec_uninit (a: Type) (n: nat) : array_spec a
val array_spec_uninit_len a n : Lemma (array_spec_len (array_spec_uninit a n) == n) [SMTPat (array_spec_len (array_spec_uninit a n))]
val array_spec_uninit_mask a n (i:nat) : Lemma (i < n ==> array_spec_mask (array_spec_uninit a n) i) [SMTPat (array_spec_mask (array_spec_uninit a n) i)]

fn alloc_array u#a (#a:Type u#a) {| small_type u#a |} (sz:SizeT.t)
  returns r : array a
  ensures freeable_array r
  ensures array_pts_to_uninit' r
  ensures pure (reveal (array_spec_of r) == array_spec_uninit a (SZ.v sz))

fn free_array u#a (#a:Type u#a) (r:array a)
  requires array_pts_to_uninit' r
  requires freeable_array r

fn stack_alloc_array u#a (#a:Type u#a) {| small_type u#a |} (sz:SizeT.t)
  returns r : array a
  ensures array_pts_to_uninit' r
  ensures pure (reveal (array_spec_of r) == array_spec_uninit a (SZ.v sz))

fn stack_free_array u#a (#a:Type u#a) (r:array a)
  requires array_pts_to_uninit' r

fn calloc_array u#a (#a:Type u#a) {| small_type u#a |} {| has_zero_default a |} (sz:SizeT.t)
  returns r : array a
  ensures freeable_array r
  ensures exists* y. array_pts_to r 1.0R y ** pure (y == array_spec_zeroed a (SizeT.v sz) zero_default)

ghost fn length_of u#a (#a: Type u#a) (x: array a) (#p: perm) (#y: array_spec a)
  preserves array_pts_to x p y
  returns n: nat
  ensures rewrites_to n (array_spec_len y)
{ array_spec_len y }

// live_array: array resource preserved across loop iterations
[@@pulse_eager_unfold]
let live_array (#t: Type u#a) (a: array t) : slprop =
  exists* (s: full_array_spec t). array_pts_to a 1.0R s

fn array_read u#a (#t: Type u#a) (a: array t) (i: SZ.t)
  (#p: perm)
  (#s: erased (array_spec t) { array_spec_initd s (SZ.v i) /\ array_spec_mask s (SZ.v i) })
  preserves array_pts_to a p s
  returns res: t
  ensures rewrites_to res (array_spec_idx s (SZ.v i))

val array_spec_upd (#a: Type) (s: array_spec a) (n: nat) (x: a) : array_spec a
val array_spec_upd_len #a s n x : Lemma (array_spec_len (array_spec_upd #a s n x) == array_spec_len s) [SMTPat (array_spec_len (array_spec_upd #a s n x))]
val array_spec_upd_initd #a s n x (i:nat) : Lemma (array_spec_initd (array_spec_upd #a s n x) i <==> (i == n /\ i < array_spec_len s) \/ array_spec_initd s i) [SMTPat (array_spec_initd (array_spec_upd #a s n x) i)]
val array_spec_upd_mask #a s n x (i:nat) :
  Lemma (array_spec_mask (array_spec_upd #a s n x) i <==> array_spec_mask s i \/ (i == n /\ n < array_spec_len s)) [SMTPat (array_spec_mask (array_spec_upd #a s n x) i)]
val array_spec_upd_idx1 #a s n x (i:nat) : Lemma (i =!= n /\ array_spec_initd s i ==> (array_spec_idx (array_spec_upd #a s n x) i == array_spec_idx s i)) [SMTPat (array_spec_idx (array_spec_upd #a s n x) i)]
val array_spec_upd_idx2 #a s (n:nat) x : Lemma (n < array_spec_len s ==> array_spec_idx (array_spec_upd #a s n x) n == x) [SMTPat (array_spec_idx (array_spec_upd #a s n x) n)]

let list_length_nil #a : Lemma (List.length ([] <: list a) == 0) [SMTPat (List.length ([] <: list a))] = ()
let list_length_cons #a (x: a) (xs: list a) : Lemma (List.length (x :: xs) == List.length xs + 1) [SMTPat (List.length (x :: xs))] = ()
let list_index_zero #a (x: a) (xs: list a) : Lemma (List.Tot.index (x::xs) 0 == x) [SMTPat (List.Tot.index (x::xs) 0)] = ()
let list_index_pos #a (x: a) (xs: list a) (i: nat) :
  Lemma
    (requires 0 < i /\ i < List.length xs + 1)
    (ensures List.Tot.index (x::xs) i == List.Tot.index xs (i-1))
    [SMTPat (List.Tot.index (x::xs) i)] =
  ()

val array_spec_of_list (#a: Type) (xs: list a) : full_array_spec a

val array_spec_of_list_full_len (#a: Type) (xs: list a) :
  Lemma (array_spec_len (array_spec_of_list xs) == List.length xs)
  [SMTPat (array_spec_of_list xs)]

val array_spec_of_list_idx #a (xs: list a) (i: nat) :
  Lemma
    (requires i < List.length xs)
    (ensures array_spec_idx (array_spec_of_list xs) i == List.Tot.index xs i)
    [SMTPat (array_spec_idx (array_spec_of_list xs) i)]

let array_spec_len_of_list #a (#xs: list a) #n (h: List.length xs == n) : (array_spec_len (array_spec_of_list xs) == n) = ()

val array_spec_to_list #a (s: full_array_spec a) : list a
val array_spec_to_list_len #a s : Lemma (List.length (array_spec_to_list #a s) == array_spec_len s) [SMTPat (List.length (array_spec_to_list #a s))]
val array_spec_to_list_idx #a (s: full_array_spec a) (i: nat) :
  Lemma
    (requires i < array_spec_len s)
    (ensures List.Tot.index (array_spec_to_list s) i == array_spec_idx s i)
    [SMTPat (List.Tot.index (array_spec_to_list s) i)]
val array_spec_to_list_of_list #a (xs: list a) :
  Lemma (array_spec_to_list (array_spec_of_list xs) == xs)
    [SMTPat (array_spec_to_list (array_spec_of_list xs))]

fn array_write u#a (#t: Type u#a) (a: array t) (i: SZ.t) (v: t)
  (#s: erased (array_spec t) { array_spec_mask s (SZ.v i) })
  requires array_pts_to a 1.0R s
  ensures exists* s'. array_pts_to a 1.0R s' ** pure (s' == array_spec_upd s (SZ.v i) v)

fn array_assign_ret u#a (#t: Type u#a) (a: array t) (i: SZ.t) (v: t)
  (#s: erased (array_spec t) { array_spec_mask s (SZ.v i) })
  requires array_pts_to a 1.0R s
  returns v': t
  ensures exists* s'. array_pts_to a 1.0R s' ** pure (s' == array_spec_upd s (SZ.v i) v) ** rewrites_to v' v

fn array_update u#a (#t #s: Type u#a) (a: array t) (i: SZ.t) (upd: (t -> s -> t)) (y: s)
  (#sp: erased (array_spec t) { array_spec_initd sp (SZ.v i) /\ array_spec_mask sp (SZ.v i) })
  requires array_pts_to a 1.0R sp
  ensures exists* sp'. array_pts_to a 1.0R sp' **
    pure (sp' == array_spec_upd sp (SZ.v i) (upd (array_spec_idx sp (SZ.v i)) y))

// ---------------------------------------------------------------------------
// ArrayPtr: pointers into arrays (zero-length sub-arrays sharing a base)
//
// An arrayptr is just a Pulse array with length 0 and the same base as its
// parent. arrayptr_pts_to is a pure proposition asserting this relationship.
// ---------------------------------------------------------------------------

val length #t (a: array t) : GTot nat
val base_of #t (a: array t) : base_t
val offset_of #t (a: array t) : GTot nat

/// Offset of x relative to y (may be negative).
private let arrayptr_off (#t: Type) (x y: array t) : GTot int =
  offset_of x - offset_of y

/// Predicate asserting that arrayptr `x` points into array `y`.
/// Same base, zero length.
let arrayptr_pts_to (#t: Type u#a) ([@@@mkey] x: array t) (y: array t) : slprop =
  pure (base_of x == base_of y /\ length x == 0)

let arrayptr_parent #a (x: array a) #y =
  observe (arrayptr_pts_to x) #y

ghost fn arrayptr_pts_to_dup u#a (#t: Type u#a) x y : duplicable_f (arrayptr_pts_to u#a #t x y) = {
  unfold arrayptr_pts_to x y;
  fold arrayptr_pts_to x y;
  fold arrayptr_pts_to x y;
}

instance val duplicable_arrayptr_pts_to #t x y : duplicable (arrayptr_pts_to #t x y)

/// Create an arrayptr from an array at offset `i`.
val array_to_arrayptr (#t: Type u#a) (arr: array t) (i: SZ.t)
  : stt (array t)
    emp
    (fun r -> arrayptr_pts_to r arr ** pure (base_of r == base_of arr /\ offset_of r == offset_of arr + SZ.v i))

/// Shift an arrayptr by `n` positions.
val arrayptr_shift (#t: Type u#a) (x: array t) (n: SZ.t) (#y: erased (array t))
  : stt (array t)
    (arrayptr_pts_to x y)
    (fun r -> arrayptr_pts_to x y ** arrayptr_pts_to r y **
      pure (base_of r == base_of x /\ offset_of r == offset_of x + SZ.v n))

/// Read through an arrayptr at index `i`, borrowing permissions from parent `y`.
fn arrayptr_read u#a (#t: Type u#a) (x: array t) (i: SZ.t)
  (#y: erased (array t))
  (#p: perm) (#s: erased (array_spec t) { 0 <= arrayptr_off x y + SZ.v i /\ array_spec_initd s (arrayptr_off x y + SZ.v i) })
  requires arrayptr_pts_to x y
  preserves array_pts_to y p s
  returns res: t
  ensures rewrites_to res (array_spec_idx s (arrayptr_off x y + SZ.v i))

/// Write through an arrayptr at index `i`, using permissions from parent `y`.
fn arrayptr_write u#a (#t: Type u#a) (x: array t) (i: SZ.t) (v: t)
  (#y: erased (array t))
  (#s: erased (array_spec t) { 0 <= arrayptr_off x y + SZ.v i /\ array_spec_mask s (arrayptr_off x y + SZ.v i) })
  requires arrayptr_pts_to x y
  requires array_pts_to y 1.0R s
  ensures exists* s'.
    array_pts_to y 1.0R s' **
    pure (s' == array_spec_upd s (arrayptr_off x y + SZ.v i) v)

fn arrayptr_assign_ret u#a (#t: Type u#a) (x: array t) (i: SZ.t) (v: t)
  (#y: erased (array t))
  (#s: erased (array_spec t) { 0 <= arrayptr_off x y + SZ.v i /\ array_spec_mask s (arrayptr_off x y + SZ.v i) })
  requires arrayptr_pts_to x y
  requires array_pts_to y 1.0R s
  returns v': t
  ensures exists* s'.
    array_pts_to y 1.0R s' **
    pure (s' == array_spec_upd s (arrayptr_off x y + SZ.v i) v) **
    rewrites_to v' v

fn arrayptr_update u#a (#t #s: Type u#a) (x: array t) (i: SZ.t) (upd: (t -> s -> t)) (y: s)
  (#arr: erased (array t))
  (#sp: erased (array_spec t) { 0 <= arrayptr_off x arr + SZ.v i /\
    array_spec_initd sp (arrayptr_off x arr + SZ.v i) /\
    array_spec_mask sp (arrayptr_off x arr + SZ.v i) })
  requires arrayptr_pts_to x arr
  requires array_pts_to arr 1.0R sp
  ensures exists* sp'.
    array_pts_to arr 1.0R sp' **
    pure (sp' == array_spec_upd sp (arrayptr_off x arr + SZ.v i)
      (upd (array_spec_idx sp (arrayptr_off x arr + SZ.v i)) y))

/// Subtract two arrayptrs to get their offset difference.
val arrayptr_diff (#t: Type) (x z: array t)
  : (r:Pulse.Lib.C.PtrdiffT.t{Pulse.Lib.C.PtrdiffT.v r == offset_of x - offset_of z})

/// Compare two arrayptrs for equality.
val arrayptr_eq (#t: Type) (x z: array t) :
  Pure bool (requires True) (ensures fun r -> offset_of x == offset_of z)

/// Check if arrayptr x offset is <= z offset.
val arrayptr_lte (#t: Type) (x z: array t) :
  Pure bool (requires base_of x == base_of z) (ensures fun r -> offset_of x <= offset_of z)

/// Check if arrayptr x offset is < z offset.
val arrayptr_lt (#t: Type) (x z: array t) :
  Pure bool (requires base_of x == base_of z) (ensures fun r -> offset_of x < offset_of z)

/// Drop an arrayptr_pts_to predicate (for scope exit / cleanup).
ghost fn arrayptr_drop u#a (#t: Type u#a) (x: array t) (#y: array t)
  requires arrayptr_pts_to x y
{}