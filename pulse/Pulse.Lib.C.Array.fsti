module Pulse.Lib.C.Array
open Pulse
open Pulse.Lib.C.Inhabited
open Pulse.Lib.SmallType
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module MU = Pulse.Lib.C.MaybeUninit
module CR = Pulse.Lib.C.CoreRef

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
let full_array_lspec a (l: nat) = s:full_array_spec a { array_spec_len s == l }

// C string literals have static storage duration. PAL exposes only their address
// here; clients still need an explicit model before dereferencing a literal
// returned through an ownership-free (`_plain`) pointer.
val array_literal_to_ref #a #n (s: full_array_lspec a n) : Tot (R.ref a)

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

// The optional value of cell `i`: `Some x` if initialized to `x`, `None` if
// masked-but-uninitialized or out of bounds. This is the ownership value handed
// out by `array_borrow_cell` (as `MU.pts_to_maybe_uninit`).
let array_spec_get #a (s: array_spec a) (i: nat) : GTot (option a) =
  if i < array_spec_len s then Seq.index (array_spec_seq s) i else None

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

// Intro/elim bridging the `array_pts_to a 1.0R y ** pure (array_spec_full_mask y)`
// view (held after fully writing a buffer) and the packaged
// `array_pts_to_uninit'` that alloc/free/stack APIs traffic in.
ghost fn intro_array_pts_to_uninit' u#a (#t: Type u#a)
      (a: array t) (#y: erased (array_spec t))
  requires array_pts_to a 1.0R y ** pure (array_spec_full_mask (reveal y))
  ensures array_pts_to_uninit' a

ghost fn elim_array_pts_to_uninit' u#a (#t: Type u#a) (a: array t)
  requires array_pts_to_uninit' a
  returns  y : erased (array_spec t)
  ensures  array_pts_to a 1.0R (reveal y) ** pure (array_spec_full_mask (reveal y))

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

fn stack_alloc_array_full u#a (#a: Type u#a) {| small_type u#a |} (s: full_array_spec a)
  returns r : array a
  ensures array_pts_to_full r 1.0R s

fn stack_free_array_full u#a (#a: Type u#a) (r: array a) (#s: erased (full_array_spec a))
  requires array_pts_to_full r 1.0R s

fn calloc_array u#a (#a:Type u#a) {| small_type u#a |} {| has_zero_default a |} (sz:SizeT.t)
  returns r : array a
  ensures freeable_array r
  ensures exists* y. array_pts_to r 1.0R y ** pure (y == array_spec_zeroed a (SizeT.v sz) zero_default)

// Fill every cell of a fully-initialized array with `v` (C `memset`).
// Only byte-sized element types are translated to this (the transpiler rejects
// multi-byte element types), so an element-wise fill matches C's byte-wise
// semantics. The array must already be fully masked and initialized: array
// function parameters satisfy this (`array_pts_to_full`).
fn memset (#t: Type0) (a: array t) (v: t) (n: SizeT.t)
  (#s: erased (array_spec t) { array_spec_full s /\ array_spec_len s == SizeT.v n })
  requires array_pts_to a 1.0R s
  ensures array_pts_to_full a 1.0R (array_spec_zeroed t (SizeT.v n) v)


ghost fn length_of u#a (#a: Type u#a) (x: array a) (#p: perm) (#y: array_spec a)
  preserves array_pts_to x p y
  returns n: nat
  ensures rewrites_to n (array_spec_len y)
{ array_spec_len y }

ghost fn array_pts_to_not_null u#a (#a: Type u#a) (r: array a) (#p: perm) (#v: array_spec a)
  preserves array_pts_to r p v
  ensures pure (not (array_is_null r))

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

val array_spec_full_mask_upd #a (s: array_spec a) (n: nat) (x: a) :
  Lemma (requires array_spec_full_mask s)
        (ensures  array_spec_full_mask (array_spec_upd s n x))

// `array_spec_set s n w`: set cell `n` to the optional value `w`. Generalizes
// `array_spec_upd` to allow setting a cell back to uninitialized (`None`); it is
// the spec restored by returning a cell borrowed via `array_borrow_cell`.
val array_spec_set (#a: Type) (s: array_spec a) (n: nat) (w: option a) : array_spec a
val array_spec_set_len #a s n w : Lemma (array_spec_len (array_spec_set #a s n w) == array_spec_len s) [SMTPat (array_spec_len (array_spec_set #a s n w))]
val array_spec_set_mask #a s n w (i:nat) :
  Lemma (array_spec_mask (array_spec_set #a s n w) i <==> array_spec_mask s i \/ (i == n /\ n < array_spec_len s)) [SMTPat (array_spec_mask (array_spec_set #a s n w) i)]
val array_spec_set_initd #a s n w (i:nat) :
  Lemma (array_spec_initd (array_spec_set #a s n w) i <==> (i == n /\ i < array_spec_len s /\ Some? w) \/ (i =!= n /\ array_spec_initd s i)) [SMTPat (array_spec_initd (array_spec_set #a s n w) i)]
val array_spec_set_idx1 #a s n w (i:nat) : Lemma (i =!= n /\ array_spec_initd s i ==> (array_spec_idx (array_spec_set #a s n w) i == array_spec_idx s i)) [SMTPat (array_spec_idx (array_spec_set #a s n w) i)]
val array_spec_set_idx2 #a s (n:nat) x : Lemma (n < array_spec_len s ==> array_spec_idx (array_spec_set #a s n (Some x)) n == x) [SMTPat (array_spec_idx (array_spec_set #a s n (Some x)) n)]

// `array_spec_get` in terms of the primitive projections: an initialized cell
// reads back as `Some` of its value, anything else as `None`. Lets callers of
// `array_borrow_cell` recover a readable `ref` (via `MU.reveal_maybe`) when the
// borrowed cell is known initialized.
val array_spec_get_spec #a (s: array_spec a) (i: nat) :
  Lemma (array_spec_get s i == (if array_spec_initd s i then Some (array_spec_idx s i) else None))
    [SMTPat (array_spec_get s i)]

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

val array_spec_of_list_len #a (xs: list a) :
  Lemma (array_spec_len (array_spec_of_list xs) == List.length xs)
    [SMTPat (array_spec_of_list xs)]

val array_spec_of_list_idx #a (xs: list a) (i: nat) :
  Lemma
    (requires i < List.length xs)
    (ensures array_spec_idx (array_spec_of_list xs) i == List.Tot.index xs i)
    [SMTPat (array_spec_idx (array_spec_of_list xs) i)]

let array_spec_of_list_with_len (#a: Type) (xs: list a) (n: nat) (#_: normalize_term (List.length xs) == n) :
    full_array_lspec a n =
  array_spec_of_list xs

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

/// Bridge between the handle's `length` and the spec's `array_spec_len`.
/// `array_pts_to` is defined on top of `pts_to_mask`, whose length info
/// is otherwise hidden by the abstraction; this exposes it so downstream
/// proofs can discharge offset-bound VCs that compare a static
/// `length x == K` refinement against `array_spec_len y`.
ghost fn array_pts_to_len u#a (#a: Type u#a) (x: array a)
                              (#p: perm) (#y: array_spec a)
  preserves array_pts_to x p y
  ensures pure (length x == array_spec_len y)

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

/// An arrayptr into a non-null array is itself non-null.
/// (The base model only states the null=>null direction via `gsub_null`;
/// this is the missing non-null=>non-null direction.)
ghost fn arrayptr_pts_to_not_null u#a (#t: Type u#a) (r: array t) (#arr: array t)
  preserves arrayptr_pts_to r arr
  requires pure (not (array_is_null arr))
  ensures pure (not (array_is_null r))

/// Surface the pure witness facts carried by `arrayptr_pts_to`: parent base
/// equality and zero length. `array_to_arrayptr` exposes `base_of` directly,
/// but `length x == 0` is otherwise trapped inside the (folded) predicate and
/// framed away unless extracted.
ghost fn arrayptr_pts_to_facts u#a (#t: Type u#a) (x: array t) (#y: array t)
  preserves arrayptr_pts_to x y
  ensures pure (base_of x == base_of y /\ length x == 0)

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

/// Subtract two arrayptrs to get their offset difference. In C, pointer
/// subtraction is only defined when both operands point into the *same* array
/// object (C11 6.5.6p9), and the result must be representable in `ptrdiff_t`
/// (6.5.6p9: otherwise the behavior is undefined). Both facts are required
/// here: the same-base requirement mirrors the sibling comparisons
/// `arrayptr_lt`/`arrayptr_lte`, and the `fits` requirement keeps the result
/// type inhabited (`PtrdiffT.v` is bounded to `Int64`, but `offset_of` is an
/// unbounded `nat`, so without it the postcondition could be uninhabited).
val arrayptr_diff (#t: Type) (x z: array t) :
  Pure Pulse.Lib.C.PtrdiffT.t
    (requires base_of x == base_of z /\ Pulse.Lib.C.PtrdiffT.fits (offset_of x - offset_of z))
    (ensures fun r -> Pulse.Lib.C.PtrdiffT.v r == offset_of x - offset_of z)

/// Compare two arrayptrs for equality. Two pointers are equal iff they share a
/// base and offset. The result MUST be tied to the comparison: asserting the
/// relation unconditionally (ignoring `r`) is unsound -- it would let a caller
/// derive e.g. `offset_of x == offset_of z` for distinct pointers.
val arrayptr_eq (#t: Type) (x z: array t) :
  Pure bool (requires True)
    (ensures fun r -> r <==> (base_of x == base_of z /\ offset_of x == offset_of z))

/// Check if arrayptr x offset is <= z offset.
val arrayptr_lte (#t: Type) (x z: array t) :
  Pure bool (requires base_of x == base_of z) (ensures fun r -> r <==> offset_of x <= offset_of z)

/// Check if arrayptr x offset is < z offset.
val arrayptr_lt (#t: Type) (x z: array t) :
  Pure bool (requires base_of x == base_of z) (ensures fun r -> r <==> offset_of x < offset_of z)

/// View an array/arrayptr as a `ref` of the same pointee. An arrayptr and a
/// `ref` share the same underlying handle (`ref t == array t`), so this is the
/// identity coercion -- no runtime primitive is required. PAL emits it when a
/// mixed arrayptr/ref `==` is elaborated: the arrayptr operand is converted to
/// a `ref` and then both operands erase to their raw machine address via the
/// single `CR.ref_to_core` primitive, compared with `CR.core_ref_eq` -- true
/// iff they name the same location. It reads nothing (needs no `pts_to`), so a
/// non-owning arrayptr may be converted.
val array_to_ref (#t: Type u#a) (r: array t) : R.ref t

/// Drop an arrayptr_pts_to predicate (for scope exit / cleanup).
ghost fn arrayptr_drop u#a (#t: Type u#a) (x: array t) (#y: array t)
  requires arrayptr_pts_to x y
{}
// ---------------------------------------------------------------------------
// Borrowing a single cell of an array as a `ref`.
//
// PAL emits `array_borrow_cell` to turn a C `&a[i]` (address of an array
// element) into a Pulse `ref` when it flows into a plain-pointer parameter.
// The borrowed cell is removed from the array's mask by moving its spec cell to
// `OutOfMask` (`array_spec_borrow`): the array then holds `array_pts_to a p
// (array_spec_borrow s i)`, i.e. every cell but `i`. `array_return_cell` puts
// it back, possibly with an updated value. No separate `pts_to` predicate is
// needed -- the mask in `array_pts_to` already exists to lend a cell's
// ownership out of the array.
//
// A single pair of lemmas handles both initialized and uninitialized cells: the
// borrowed cell is handed out as `MU.pts_to_maybe_uninit r (array_spec_get s i)`
// (`Some x` for an initialized cell, recoverable as a readable `ref` via
// `MU.reveal_maybe`; `None` for an uninitialized one, usable as an `_out` ref via
// `MU.forget_maybe`), and returned as `MU.pts_to_maybe_uninit ... w`, restoring
// the cell to `array_spec_set s i w`.
// ---------------------------------------------------------------------------

/// `s` with cell `i` removed from the mask (its ownership lent out). This is
/// just the existing mask machinery: cell `i` becomes `OutOfMask`, so
/// `array_pts_to a p (array_spec_borrow s i)` is the array owning every cell
/// but `i`.
val array_spec_borrow (#a: Type u#a) (s: array_spec a) (i: nat) : array_spec a

/// Ghost ref aliasing cell `i` of `a` (defaulted so it is well-typed without a
/// `i < length a` hypothesis). Used to name the borrowed cell across the
/// borrow/return boundary.
val array_cell_ref (#t: Type u#a) (a: array t) (i: nat) : GTot (ref t)

/// Borrow cell `i` of `a` as a `ref`, for any initialization state, removing it
/// from the array's mask. The cell is handed out as `MU.pts_to_maybe_uninit`
/// carrying its current optional value. Requires full permission (the
/// uninitialized case yields a writable, full-permission cell).
fn array_borrow_cell u#a (#t: Type u#a) (a: array t) (i: SZ.t)
  (#s: erased (array_spec t) { array_spec_mask s (SZ.v i) })
  requires array_pts_to a 1.0R s
  returns r: ref t
  ensures MU.pts_to_maybe_uninit r (array_spec_get s (SZ.v i))
  ensures array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
  ensures rewrites_to r (array_cell_ref a (SZ.v i))

/// Adapt a cell borrowed by `array_borrow_cell` (handed out as
/// `MU.pts_to_maybe_uninit`) that is known initialized into a readable `ref`
/// (`pts_to`). Applied by the user (via inline Pulse) when a borrowed cell must
/// flow into a readable pointer parameter; the readable-side dual of
/// `MU.forget_maybe` (which auto-fires via `[@@pulse_intro]` for `_out`
/// parameters). The array resource pins down the erased spec `s`.
ghost
fn array_cell_read u#a (#t: Type u#a) (a: array t) (i: SZ.t)
  (#s: erased (array_spec t) { array_spec_initd s (SZ.v i) })
  requires array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
  requires MU.pts_to_maybe_uninit (array_cell_ref a (SZ.v i)) (array_spec_get s (SZ.v i))
  ensures array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
  ensures (array_cell_ref a (SZ.v i) |-> array_spec_idx s (SZ.v i))

/// Return a borrowed cell, writing its optional value `w` back into the array
/// (`Some x` restores an initialized cell, `None` an uninitialized one).
/// Invoked manually from C via `_ghost_stmt`. The cell index `i` is *inferred*
/// from the borrowed-cell / carved-array resources in context rather than passed
/// explicitly, so this returns a cell borrowed at any index -- including the
/// symbolic offset of a cell borrowed via an arrayptr (`arrayptr_off x a`),
/// which a hard-coded literal index could not unify against.
ghost
fn array_return_cell u#a (#t: Type u#a) (a: array t)
  (#i: nat)
  (#w: option t)
  (#s: erased (array_spec t) { array_spec_mask s i })
  requires MU.pts_to_maybe_uninit (array_cell_ref a i) w
  requires array_pts_to a 1.0R (array_spec_borrow s i)
  ensures array_pts_to a 1.0R (array_spec_set s i w)

// ---------------------------------------------------------------------------
// Borrowing the cell an arrayptr points at, out of its live parent array.
//
// An arrayptr `x` into `y` (`arrayptr_pts_to x y`) names a location but owns
// nothing (`arrayptr_pts_to` is pure and duplicable). To pass such a pointer
// where a plain `ref` is expected, the ownership of the pointed-at cell is
// *borrowed* from the still-live parent array `y` (which must be in scope as
// `array_pts_to y 1.0R s`) -- exactly as `array_borrow_cell` does for a literal
// `&a[i]`, but with the index taken from the arrayptr's own offset into its
// parent, `arrayptr_off x y`. The cell is given back by the user (via
// `_ghost_stmt`) with either `arrayptr_return_cell` (which needs the arrayptr
// handle) or, when no named arrayptr survives, the index-inferring
// `array_return_cell`. PAL emits `arrayptr_borrow_cell` for a plain-pointer
// local initialized from an arrayptr (`T* p = <arrayptr>;`); it emits no ghost
// return of its own.
// ---------------------------------------------------------------------------

/// Borrow the cell at arrayptr `x`'s position out of its parent array `y`, as a
/// `ref` handed out as `MU.pts_to_maybe_uninit` (the arrayptr analogue of
/// `array_borrow_cell`). The parent must be live at full permission; the
/// arrayptr link `arrayptr_pts_to x y` is preserved so the cell can later be
/// returned with `arrayptr_return_cell` (or, when the arrayptr handle does not
/// survive -- e.g. the arrayptr was an anonymous, inlined call result -- with
/// the index-inferring `array_return_cell`).
fn arrayptr_borrow_cell u#a (#t: Type u#a) (x: array t)
  (#y: erased (array t))
  (#s: erased (array_spec t) { 0 <= arrayptr_off x y /\ array_spec_mask s (arrayptr_off x y) })
  requires arrayptr_pts_to x y
  requires array_pts_to y 1.0R s
  returns r: ref t
  ensures arrayptr_pts_to x y
  ensures MU.pts_to_maybe_uninit r (array_spec_get s (arrayptr_off x y))
  ensures array_pts_to y 1.0R (array_spec_borrow s (arrayptr_off x y))
  ensures rewrites_to r (array_cell_ref y (arrayptr_off x y))

/// Return a cell borrowed with `arrayptr_borrow_cell`, writing its optional
/// value `w` back into the parent array `y` (the arrayptr analogue of
/// `array_return_cell`). Invoked manually by the user (via `_ghost_stmt`); the
/// index-inferring `array_return_cell` is the more common choice.
ghost
fn arrayptr_return_cell u#a (#t: Type u#a) (x: array t)
  (#w: option t)
  (#y: erased (array t))
  (#s: erased (array_spec t) { 0 <= arrayptr_off x y /\ array_spec_mask s (arrayptr_off x y) })
  requires arrayptr_pts_to x y
  requires MU.pts_to_maybe_uninit (array_cell_ref y (arrayptr_off x y)) w
  requires array_pts_to y 1.0R (array_spec_borrow s (arrayptr_off x y))
  ensures arrayptr_pts_to x y
  ensures array_pts_to y 1.0R (array_spec_set s (arrayptr_off x y) w)
