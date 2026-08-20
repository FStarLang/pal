module Pulse.Lib.C.Array
friend Pulse.Lib.Reference
open Pulse
open Pulse.Lib.C.Inhabited
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module MU = Pulse.Lib.C.MaybeUninit
module SZ = FStar.SizeT
#lang-pulse

let array a = A.array a
let array_null #a = A.null #a
let array_is_null #a r = A.is_null #a r

noeq type array_spec_cell t =
  | OutOfMask
  | Uninit
  | Val of t

let array_spec_t t =
  Seq.seq (array_spec_cell t)

let array_spec t = array_spec_t t

let array_spec_len #a (s: array_spec a) = Seq.length s
let array_spec_initd #a (s: array_spec a) (i: nat) : prop = i < Seq.length s /\ Val? (Seq.index s i)
let array_spec_mask #a (s: array_spec a) (i: nat) : prop = i < Seq.length s /\ ~(OutOfMask? (Seq.index s i))
let array_spec_idx #a (s: array_spec a) (i: nat { array_spec_initd s i }) : Tot a = let Val x = Seq.index s i in x

let array_literal_to_ref #a #n (_: full_array_lspec a n) : Tot (R.ref a) =
  admit ()

let to_mask #t (s: array_spec t) (i: nat) : prop = array_spec_mask s i

let to_seq #t (s: array_spec t) : GTot (Seq.seq (option t)) =
  Seq.init_ghost (Seq.length s) fun i ->
    match Seq.index s i with
    | Val x -> Some x
    | _ -> None

let array_spec_ext #a (s1 s2: array_spec a) :
  Lemma (requires
    array_spec_len s1 == array_spec_len s2
      /\ (forall (i:nat). i < array_spec_len s1 ==> (array_spec_initd s1 i <==> array_spec_initd s2 i))
      /\ (forall (i:nat). i < array_spec_len s1 ==> (array_spec_mask s1 i <==> array_spec_mask s2 i))
      /\ (forall (i:nat). i < array_spec_len s1 /\ array_spec_initd s1 i ==> array_spec_idx s1 i == array_spec_idx s2 i))
  (ensures s1 == s2)
= assert (Seq.length s1 == Seq.length s2);
  let aux (i: nat { i < Seq.length s1 }) : Lemma (Seq.index s1 i == Seq.index s2 i) =
    match Seq.index s1 i, Seq.index s2 i with
    | Val _, Val _ -> ()
    | Uninit, Uninit -> ()
    | OutOfMask, OutOfMask -> ()
    | Val _, Uninit -> ()
    | Uninit, Val _ -> ()
    | OutOfMask, _ -> ()
    | _, OutOfMask -> ()
  in
  Classical.forall_intro (Classical.move_requires aux);
  Seq.lemma_eq_intro s1 s2

let array_spec_zeroed (a: Type) (n: nat) (x: a) : array_spec a =
  Seq.init n fun _ -> Val x

let array_spec_zeroed_len a n x = ()
let array_spec_zeroed_initd a n x i = ()
let array_spec_zeroed_mask a n x i = ()
let array_spec_zeroed_idx a n x i = ()

// The slprop backing array_pts_to: we use Pulse.Lib.Array.Core.pts_to_mask
// with our to_seq/to_mask projections.
let array_pts_to #a (x: array a) (p: perm) (y: array_spec a) : slprop =
  A.pts_to_mask x #p (to_seq y) (to_mask y)

fn array_read_all u#a (#a: Type u#a) (x: array a)
  preserves array_pts_to x 'p 'y
  returns z: array_spec a
  ensures rewrites_to z 'y
{
  admit ()
}

ghost fn intro_array_pts_to_uninit' u#a (#t: Type u#a)
      (a: array t) (#y: erased (array_spec t))
  requires array_pts_to a 1.0R y ** pure (array_spec_full_mask (reveal y))
  ensures array_pts_to_uninit' a
{
  ()
}

ghost fn elim_array_pts_to_uninit' u#a (#t: Type u#a) (a: array t)
  requires array_pts_to_uninit' a
  returns  y : erased (array_spec t)
  ensures  array_pts_to a 1.0R (reveal y) ** pure (array_spec_full_mask (reveal y))
{
  observe (array_pts_to_uninit a)
}

let freeable_array #a (r: array a) : slprop =
  pure (A.is_full_array r)

let array_spec_uninit (a: Type) (n: nat) : array_spec a =
  Seq.init n fun _ -> Uninit

let array_spec_uninit_len a n = ()
let array_spec_uninit_mask a n i = ()

let array_spec_upd (#a: Type) (s: array_spec a) (n: nat) (x: a) : array_spec a =
  if n < Seq.length s
  then Seq.upd s n (Val x)
  else s

let array_spec_upd_len #a s n x = ()
let array_spec_upd_initd #a s n x i = ()
let array_spec_upd_mask #a s n x i = ()
let array_spec_upd_idx1 #a s n x i = ()
let array_spec_upd_idx2 #a s (n:nat) x = ()

let array_spec_full_mask_upd #a s n x = ()

// The spec cell corresponding to an `option` value held by `pts_to_mask`:
// `None` (no value) is an `Uninit` cell, `Some x` is `Val x`. Both are masked.
let opt_cell #t (v: option t) : array_spec_cell t =
  match v with
  | None -> Uninit
  | Some x -> Val x

// `array_spec_set s i w`: cell `i` set to the optional value `w`. `Some x`
// initializes it to `x` (`Val x`); `None` leaves it masked-but-uninitialized
// (`Uninit`). Both are masked, so this is exactly the spec that returning a cell
// borrowed by `array_borrow_cell` (as `pts_to_maybe_uninit ... w`) restores.
let array_spec_set (#a: Type) (s: array_spec a) (n: nat) (w: option a) : array_spec a =
  if n < Seq.length s then Seq.upd s n (opt_cell w) else s

let array_spec_set_len #a s n w = ()
let array_spec_set_mask #a s n w i = ()
let array_spec_set_initd #a s n w i = ()
let array_spec_set_idx1 #a s n w i = ()
let array_spec_set_idx2 #a s (n:nat) x = ()

let array_spec_get_spec #a s i = ()

let array_spec_of_list xs =
  Seq.init (List.length xs) fun i -> Val (List.Tot.index xs i)

let array_spec_of_list_len xs = ()

let array_spec_of_list_idx xs i = ()

private let rec mk_list (#a: Type) (s: full_array_spec a) (i: nat { i <= Seq.length s }) : Tot (list a)
  (decreases (Seq.length s - i))
=
  if i >= Seq.length s then []
  else array_spec_idx s i :: mk_list s (i + 1)

let array_spec_to_list #a (s: full_array_spec a) : list a =
  mk_list s 0

private let rec mk_list_length (#a: Type) (s: full_array_spec a) (i: nat) : Lemma
  (requires i <= array_spec_len s)
  (ensures List.length (mk_list s i) == array_spec_len s - i)
  (decreases (array_spec_len s - i))
=
  if i >= array_spec_len s then ()
  else mk_list_length s (i + 1)

let array_spec_to_list_len #a s =
  mk_list_length s 0

private let rec mk_list_index (#a: Type) (s: full_array_spec a) (i j: nat) : Lemma
  (requires i <= array_spec_len s /\ i + j < array_spec_len s)
  (ensures (mk_list_length s i; List.Tot.index (mk_list s i) j == array_spec_idx s (i + j)))
  (decreases j)
=
  mk_list_length s i;
  if j = 0 then ()
  else begin
    mk_list_length s (i + 1);
    mk_list_index s (i + 1) (j - 1)
  end

let array_spec_to_list_idx #a s i =
  mk_list_length s 0;
  mk_list_index s 0 i

let array_spec_to_list_of_list #a xs =
  let s = array_spec_of_list xs in
  mk_list_length s 0;
  array_spec_of_list_len xs;
  let aux (i: nat { i < List.length (mk_list s 0) }) : Lemma
    (List.Tot.index (mk_list s 0) i == List.Tot.index xs i)
  = mk_list_index s 0 i
  in
  Classical.forall_intro aux;
  List.Tot.Properties.index_extensionality (mk_list s 0) xs

fn alloc_array u#a (#a:Type u#a) {| small_type u#a |} (sz:SZ.t)
  returns r : array a
  ensures freeable_array r
  ensures array_pts_to_uninit' r
  ensures pure (reveal (array_spec_of r) == array_spec_uninit a (SZ.v sz))
{
  let r = A.mask_alloc a sz;
  with v. assert A.pts_to_mask r v _;
  assume pure (v == Seq.create (SZ.v sz) None);
  mask_mext r (to_mask (array_spec_uninit a (SZ.v sz)));
  mask_vext r (to_seq (array_spec_uninit a (SZ.v sz)));
  fold array_pts_to r 1.0R (array_spec_uninit a (SZ.v sz));
  fold freeable_array r;
  r
}

fn free_array u#a (#a:Type u#a) (r:array a)
  requires array_pts_to_uninit' r
  requires freeable_array r
{
  unfold array_pts_to r _ _;
  unfold freeable_array r;
  A.mask_mext r (fun _ -> True);
  A.mask_free r;
}

fn stack_alloc_array u#a (#a:Type u#a) {| small_type u#a |} (sz:SZ.t)
  returns r : array a
  ensures array_pts_to_uninit' r
  ensures pure (reveal (array_spec_of r) == array_spec_uninit a (SZ.v sz))
{
  let r = alloc_array #a sz;
  drop_ (freeable_array r);
  r
}

fn stack_free_array u#a (#a:Type u#a) (r:array a)
  requires array_pts_to_uninit' r
{
  assume freeable_array r;
  free_array r;
}

fn stack_alloc_array_full u#a (#a: Type u#a) {| small_type u#a |} (s: full_array_spec a)
  returns r : array a
  ensures array_pts_to_full r 1.0R s
{
  admit ()
}

fn stack_free_array_full u#a (#a: Type u#a) (r: array a) (#s: erased (full_array_spec a))
  requires array_pts_to_full r 1.0R s
{
  admit ()
}

fn calloc_array u#a (#a:Type u#a) {| small_type u#a |} {| has_zero_default a |} (sz:SZ.t)
  returns r : array a
  ensures freeable_array r
  ensures exists* y. array_pts_to r 1.0R y ** pure (y == array_spec_zeroed a (SZ.v sz) zero_default)
{
  let r = A.alloc (zero_default #a) sz;
  A.to_mask r;
  mask_mext r (to_mask (array_spec_zeroed a (SZ.v sz) zero_default));
  mask_vext r (to_seq (array_spec_zeroed a (SZ.v sz) zero_default));
  fold array_pts_to r 1.0R (array_spec_zeroed a (SZ.v sz) zero_default);
  fold freeable_array r;
  r
}

// memset: fill every cell of a fully-initialized array with `v`, mirroring the
// C `memset(a, v, sizeof(t) * n)` idiom. Built on Pulse.Lib.Array.fill, so the
// array must already be fully masked and initialized (e.g. an array function
// parameter, which is handed in as `array_pts_to_full`). The transpiler only
// targets this for byte-sized element types, so the element-wise fill matches
// C's byte-wise memset semantics.

// A fully-masked, fully-initialized spec projects to an all-masked, all-`Some`
// backing sequence, which is exactly `from_mask`'s precondition.
let full_to_mask_seq #t (s: array_spec t) (i: nat)
  : Lemma (requires array_spec_full s)
          (ensures i < array_spec_len s ==>
            to_mask s i /\ Some? (Seq.index (to_seq s) i))
= if i < array_spec_len s then begin
    assert (array_spec_initd s i);
    assert (array_spec_mask s i)
  end

fn memset (#t: Type0) (a: array t) (v: t) (n: SZ.t)
  (#s: erased (array_spec t) { array_spec_full s /\ array_spec_len s == SZ.v n })
  requires array_pts_to a 1.0R s
  ensures array_pts_to_full a 1.0R (array_spec_zeroed t (SZ.v n) v)
{
  unfold array_pts_to a 1.0R s;
  Classical.forall_intro (Classical.move_requires (full_to_mask_seq s));
  A.from_mask a;
  A.pts_to_len a;
  fill n a v;
  A.to_mask a;
  mask_mext a (to_mask (array_spec_zeroed t (SZ.v n) v));
  mask_vext a (to_seq (array_spec_zeroed t (SZ.v n) v));
  fold array_pts_to a 1.0R (array_spec_zeroed t (SZ.v n) v);
}

ghost fn array_pts_to_not_null u#a (#a: Type u#a) (r: array a) (#p: perm) (#v: array_spec a)
  preserves array_pts_to r p v
  ensures pure (not (array_is_null r))
{
  unfold array_pts_to r p v;
  A.pts_to_mask_not_null r;
  fold array_pts_to r p v;
}

fn array_read u#a (#t: Type u#a) (a: array t) (i: SZ.t)
  (#p: perm)
  (#s: erased (array_spec t) { array_spec_initd s (SZ.v i) /\ array_spec_mask s (SZ.v i) })
  preserves array_pts_to a p s
  returns res: t
  ensures rewrites_to res (array_spec_idx s (SZ.v i))
{
  // unfold array_pts_to to get pts_to_mask, then call mask_read
  unfold array_pts_to a p s;
  let r = A.mask_read a i;
  fold (array_pts_to a p s);
  r
}

#restart-solver

fn array_write u#a (#t: Type u#a) (a: array t) (i: SZ.t) (v: t)
  (#s: erased (array_spec t) { array_spec_mask s (SZ.v i) })
  requires array_pts_to a 1.0R s
  ensures exists* s'. array_pts_to a 1.0R s' ** pure (s' == array_spec_upd s (SZ.v i) v)
{
  unfold array_pts_to a 1.0R s;
  A.mask_write a i v;
  // Need to show that the updated sequence matches to_seq (array_spec_upd s (SZ.v i) v)
  // and the mask matches to_mask (array_spec_upd s (SZ.v i) v)
  let s' = hide (array_spec_upd s (SZ.v i) v);
  A.mask_mext a (to_mask s');
  A.mask_vext a (to_seq s');
  fold (array_pts_to a 1.0R s');
  ()
}

fn array_assign_ret u#a (#t: Type u#a) (a: array t) (i: SZ.t) (v: t)
  (#s: erased (array_spec t) { array_spec_mask s (SZ.v i) })
  requires array_pts_to a 1.0R s
  returns v': t
  ensures exists* s'. array_pts_to a 1.0R s' ** pure (s' == array_spec_upd s (SZ.v i) v) ** rewrites_to v' v
{
  array_write a i v;
  v
}

fn array_update u#a (#t #s: Type u#a) (a: array t) (i: SZ.t) (upd: (t -> s -> t)) (y: s)
  (#sp: erased (array_spec t) { array_spec_initd sp (SZ.v i) /\ array_spec_mask sp (SZ.v i) })
  requires array_pts_to a 1.0R sp
  ensures exists* sp'. array_pts_to a 1.0R sp' **
    pure (sp' == array_spec_upd sp (SZ.v i) (upd (array_spec_idx sp (SZ.v i)) y))
{
  let v = array_read a i;
  array_write a i (upd v y);
}

let length #t (a: array t) : GTot nat = A.length a
let base_of #t (a: array t) : base_t = A.base_of a
let offset_of #t (a: array t) : GTot nat = A.offset_of a

ghost fn array_pts_to_len u#a (#a: Type u#a) (x: array a)
                              (#p: perm) (#y: array_spec a)
  preserves array_pts_to x p y
  ensures pure (length x == array_spec_len y)
{
  unfold (array_pts_to x p y);
  A.pts_to_mask_len x;
  fold (array_pts_to x p y);
}

ghost fn arrayptr_pts_to_dup' u#a (#t: Type u#a) x y : duplicable_f (arrayptr_pts_to u#a #t x y) = {
  unfold arrayptr_pts_to x y;
  fold arrayptr_pts_to x y;
  fold arrayptr_pts_to x y;
}

instance duplicable_arrayptr_pts_to #t x y : duplicable (arrayptr_pts_to #t x y) =
  { dup_f = fun _ -> arrayptr_pts_to_dup' x y }

let array_to_arrayptr #t arr i =
  admit ()
  // Stuck: need a concrete operation to produce a zero-length sub-array.
  // gsub is ghost-only, we need a runtime pointer arithmetic primitive.

// An arrayptr into a non-null array is itself non-null. The base model only
// provides the null=>null direction (via `gsub_null`); `A.same_base_null`
// supplies the converse for arrays sharing a base.
ghost fn arrayptr_pts_to_not_null u#a (#t: Type u#a) (r: array t) (#arr: array t)
  preserves arrayptr_pts_to r arr
  requires pure (not (array_is_null arr))
  ensures pure (not (array_is_null r))
{
  unfold arrayptr_pts_to r arr;
  A.same_base_null r arr;
  fold arrayptr_pts_to r arr;
}

ghost fn arrayptr_pts_to_facts u#a (#t: Type u#a) (x: array t) (#y: array t)
  preserves arrayptr_pts_to x y
  ensures pure (base_of x == base_of y /\ length x == 0)
{
  unfold arrayptr_pts_to x y;
  fold arrayptr_pts_to x y;
}

let arrayptr_shift #t x n #y =
  admit ()
  // Stuck: need a concrete operation to shift the pointer.

let arrayptr_shift_back #t x n #y =
  admit ()
  // Stuck: need a concrete operation to shift the pointer.

fn arrayptr_post_incr u#a (#t: Type u#a) (x: R.ref (array t))
  (#v: erased (array t)) (#y: erased (array t))
  requires R.pts_to x v
  requires arrayptr_pts_to v y
  returns r: array t
  ensures exists* v'.
    R.pts_to x v' **
    arrayptr_pts_to v' y **
    arrayptr_pts_to r y **
    pure (r == reveal v /\ base_of v' == base_of (reveal v) /\ offset_of v' == offset_of (reveal v) + 1)
{
  let old = !x;
  let shifted = arrayptr_shift old 1sz;
  x := shifted;
  old
}

fn arrayptr_pre_incr u#a (#t: Type u#a) (x: R.ref (array t))
  (#v: erased (array t)) (#y: erased (array t))
  requires R.pts_to x v
  requires arrayptr_pts_to v y
  returns r: array t
  ensures exists* v'.
    R.pts_to x v' **
    arrayptr_pts_to v' y **
    arrayptr_pts_to r y **
    pure (r == v' /\ base_of v' == base_of (reveal v) /\ offset_of v' == offset_of (reveal v) + 1)
{
  let old = !x;
  let shifted = arrayptr_shift old 1sz;
  x := shifted;
  shifted
}

fn arrayptr_post_decr u#a (#t: Type u#a) (x: R.ref (array t))
  (#v: erased (array t)) (#y: erased (array t))
  requires R.pts_to x v
  requires arrayptr_pts_to v y
  requires pure (offset_of (reveal v) >= 1)
  returns r: array t
  ensures exists* v'.
    R.pts_to x v' **
    arrayptr_pts_to v' y **
    arrayptr_pts_to r y **
    pure (r == reveal v /\ base_of v' == base_of (reveal v) /\ offset_of v' == offset_of (reveal v) - 1)
{
  let old = !x;
  let shifted = arrayptr_shift_back old 1sz;
  x := shifted;
  old
}

fn arrayptr_pre_decr u#a (#t: Type u#a) (x: R.ref (array t))
  (#v: erased (array t)) (#y: erased (array t))
  requires R.pts_to x v
  requires arrayptr_pts_to v y
  requires pure (offset_of (reveal v) >= 1)
  returns r: array t
  ensures exists* v'.
    R.pts_to x v' **
    arrayptr_pts_to v' y **
    arrayptr_pts_to r y **
    pure (r == v' /\ base_of v' == base_of (reveal v) /\ offset_of v' == offset_of (reveal v) - 1)
{
  let old = !x;
  let shifted = arrayptr_shift_back old 1sz;
  x := shifted;
  shifted
}

fn arrayptr_read u#a (#t: Type u#a) (x: array t) (i: SZ.t)
  (#y: erased (array t))
  (#p: perm) (#s: erased (array_spec t) { 0 <= arrayptr_off x y + SZ.v i /\ array_spec_initd s (arrayptr_off x y + SZ.v i) })
  requires arrayptr_pts_to x y
  preserves array_pts_to y p s
  returns res: t
  ensures rewrites_to res (array_spec_idx s (arrayptr_off x y + SZ.v i))
{
  admit ()
  // Stuck: need to compute the actual index into y's backing array
  // from the arrayptr offset, unfold array_pts_to, and call mask_read
  // at the computed index. Requires showing SZ.fits for the index.
}

fn arrayptr_write u#a (#t: Type u#a) (x: array t) (i: SZ.t) (v: t)
  (#y: erased (array t))
  (#s: erased (array_spec t) { 0 <= arrayptr_off x y + SZ.v i /\ array_spec_mask s (arrayptr_off x y + SZ.v i) })
  requires arrayptr_pts_to x y
  requires array_pts_to y 1.0R s
  ensures exists* s'.
    array_pts_to y 1.0R s' **
    pure (s' == array_spec_upd s (arrayptr_off x y + SZ.v i) v)
{
  admit ()
  // Stuck: same issue as arrayptr_read — need to compute index,
  // unfold, call mask_write, then refold with updated spec.
}

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
{
  arrayptr_write x i v;
  v
}

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
{
  arrayptr_write x i (upd (arrayptr_read x i) y);
}

let arrayptr_diff #t x z = admit ()
// Stuck: need a concrete primitive to compute pointer difference.

let arrayptr_eq #t x z = admit ()
// Stuck: need a concrete pointer equality primitive.

let arrayptr_lte #t x z = admit ()
// Stuck: need a concrete pointer comparison primitive.

let arrayptr_lt #t x z = admit ()
// Stuck: need a concrete pointer comparison primitive.

let array_to_ref #t r = r
// An arrayptr/array and a `ref` share the same underlying handle
// (`ref a == array a`, exposed here via `friend Pulse.Lib.Reference`), so this
// coercion is the identity -- no primitive needed. It lets a mixed
// arrayptr/ref `==` erase the arrayptr operand to a `ref` and then reuse the
// single raw-address primitive `CR.ref_to_core` (cf. `array_to_arrayptr`).

// ---------------------------------------------------------------------------
// Borrowing a single cell of an array as a `ref` (and returning it).
//
// PAL emits `array_borrow_cell` when a C `&a[i]` (address of an array element)
// flows into a parameter typed as a plain pointer (Pulse `ref`). The cell is
// removed from the array's mask while it is borrowed by moving its spec cell to
// `OutOfMask` (`array_spec_borrow`); the array then holds `array_pts_to a p
// (array_spec_borrow s i)`. `array_return_cell` puts it back, possibly with an
// updated value. No dedicated predicate is needed: the mask that backs
// `array_pts_to` already exists to lend a single cell's ownership out.
//
// These wrap `Pulse.Lib.Reference.array_at` / `return_array_at`, which operate
// on the very `pts_to_mask` that backs `array_pts_to`.
// ---------------------------------------------------------------------------

// `array_spec_borrow s i`: cell `i` moved out of the mask (its ownership lent
// out as a ref). Reuses the `OutOfMask` spec cell, so `array_pts_to a p
// (array_spec_borrow s i)` is exactly the array owning every cell but `i`.
let array_spec_borrow (#a: Type u#a) (s: array_spec a) (i: nat) : array_spec a =
  if i < Seq.length s then Seq.upd s i OutOfMask else s

// Borrowing changes only one cell, so the length is preserved.
let array_spec_borrow_len #t (s: array_spec t) (i: nat)
  : Lemma (Seq.length (array_spec_borrow s i) == Seq.length s)
          [SMTPat (Seq.length (array_spec_borrow s i))]
= ()

// Cell `i` reads back as `OutOfMask`; every other cell is untouched. This
// SMTPat lets the solver derive the mask/initd/idx facts about a borrowed spec.
let array_spec_borrow_index #t (s: array_spec t) (i: nat) (k: nat { k < Seq.length s })
  : Lemma (requires i < Seq.length s)
          (ensures Seq.index (array_spec_borrow s i) k ==
            (if k = i then OutOfMask else Seq.index s k))
          [SMTPat (Seq.index (array_spec_borrow s i) k)]
= if k = i then Seq.lemma_index_upd1 s i OutOfMask
  else Seq.lemma_index_upd2 s i OutOfMask k

// The backing sequence of a borrowed spec: cell `i` reads back as `None`
// (unowned), the rest unchanged.
let to_seq_borrow #t (s: array_spec t) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures to_seq (array_spec_borrow s i) `Seq.equal` Seq.upd (to_seq s) i None)
= ()

// Total (refinement-free) view of the ghost ref that aliases cell `i` of `a`.
// `R.array_at_ghost` needs `i < length a`, which the abstract `array_pts_to`
// hides from spec contexts; wrapping it in a default lets us name the borrowed
// cell's ref in specs without a length hypothesis. When the array resource is
// in scope (so `i < length a`), it coincides with `R.array_at_ghost a i`.
let array_cell_ref (#t: Type u#a) (a: array t) (i: nat) : GTot (ref t) =
  if i < A.length a then R.array_at_ghost a i else R.null

// The internal backing sequence `to_seq` coincides with the public projection
// `array_spec_seq` (both map `Val x -> Some x`, everything else -> `None`). This
// bridges `MU.array_at_maybe`'s result (stated over `to_seq`) to the public
// `array_spec_get` in `array_borrow_cell`'s postcondition.
let to_seq_eq_spec_seq #t (s: array_spec t)
  : Lemma (to_seq s `Seq.equal` array_spec_seq s)
= ()

// Setting cell `i` to `opt_cell vi` makes the backing sequence hold `vi` at `i`.
let to_seq_upd_opt #t (s: array_spec t) (i: nat) (vi: option t)
  : Lemma (requires i < array_spec_len s)
          (ensures to_seq (Seq.upd s i (opt_cell vi)) `Seq.equal` Seq.upd (to_seq s) i vi)
= ()

// The backing sequence of `array_spec_set s i w`: cell `i` reads back as `w`.
let to_seq_set #t (s: array_spec t) (i: nat) (w: option t)
  : Lemma (requires i < array_spec_len s)
          (ensures to_seq (array_spec_set s i w) `Seq.equal` Seq.upd (to_seq s) i w)
= to_seq_upd_opt s i w

// Borrow cell `i` of `a` as a `ref`, for any initialization state. The cell is
// carved out of the array's mask (`array_spec_borrow`) and handed back as
// `MU.pts_to_maybe_uninit` carrying its current optional value: `Some x` for an
// initialized cell (recoverable as a readable `ref` via `MU.reveal_maybe`),
// `None` for an uninitialized one. This is the single generalization of the old
// init/uninit borrows; the executable carve is the same, so no run-time branch
// on the (ghost) init state is needed. Requires full permission, because the
// uninitialized case yields a writable, full-permission cell.
fn array_borrow_cell u#a (#t: Type u#a) (a: array t) (i: SZ.t)
  (#s: erased (array_spec t) { array_spec_mask s (SZ.v i) })
  requires array_pts_to a 1.0R s
  returns r: ref t
  ensures MU.pts_to_maybe_uninit r (array_spec_get s (SZ.v i))
  ensures array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
  ensures rewrites_to r (array_cell_ref a (SZ.v i))
{
  unfold array_pts_to a 1.0R s;
  A.pts_to_mask_len a;
  let r = MU.array_at_maybe a i;
  to_seq_eq_spec_seq s;
  to_seq_borrow s (SZ.v i);
  A.mask_vext a (to_seq (array_spec_borrow s (SZ.v i)));
  A.mask_mext a (to_mask (array_spec_borrow s (SZ.v i)));
  fold (array_pts_to a 1.0R (array_spec_borrow s (SZ.v i)));
  r
}

// Adapt a cell borrowed via `array_borrow_cell` that is known initialized into a
// readable `ref` (`pts_to`). `array_borrow_cell` always hands the cell out as
// `pts_to_maybe_uninit`; the user applies this (via inline Pulse) when the
// borrowed cell must flow into a readable pointer parameter, as the readable-side
// dual of `MU.forget_maybe` (which auto-fires via `[@@pulse_intro]` for `_out`
// parameters). The array resource left by the borrow pins down the erased spec
// `s`, and the `array_spec_initd` refinement (from the
// caller's full-array knowledge) turns the maybe value into `Some`, so
// `MU.reveal_maybe` applies.
ghost
fn array_cell_read u#a (#t: Type u#a) (a: array t) (i: SZ.t)
  (#s: erased (array_spec t) { array_spec_initd s (SZ.v i) })
  requires array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
  requires MU.pts_to_maybe_uninit (array_cell_ref a (SZ.v i)) (array_spec_get s (SZ.v i))
  ensures array_pts_to a 1.0R (array_spec_borrow s (SZ.v i))
  ensures (array_cell_ref a (SZ.v i) |-> array_spec_idx s (SZ.v i))
{
  array_spec_get_spec s (SZ.v i);
  rewrite (MU.pts_to_maybe_uninit (array_cell_ref a (SZ.v i)) (array_spec_get s (SZ.v i)))
       as (MU.pts_to_maybe_uninit (array_cell_ref a (SZ.v i)) (Some (array_spec_idx s (SZ.v i))));
  MU.reveal_maybe (array_cell_ref a (SZ.v i));
}

// Return a cell borrowed with `array_borrow_cell`, writing its optional value
// `w` back into the array. `Some x` restores an initialized cell (`Val x`),
// `None` an uninitialized one (`Uninit`); either way the array comes back as
// `array_spec_set s i w`, with no `full_mask` side condition. This is the single
// generalization of the old init/uninit returns. Invoked manually from C via
// `_ghost_stmt` (the borrower packages the ref as `pts_to_maybe_uninit`, e.g.
// with `MU.intro_maybe_some` after writing a value).
ghost
fn array_return_cell u#a (#t: Type u#a) (a: array t)
  (#i: nat)
  (#w: option t)
  (#s: erased (array_spec t) { array_spec_mask s i })
  requires MU.pts_to_maybe_uninit (array_cell_ref a i) w
  requires array_pts_to a 1.0R (array_spec_borrow s i)
  ensures array_pts_to a 1.0R (array_spec_set s i w)
{
  unfold array_pts_to a 1.0R (array_spec_borrow s i);
  A.pts_to_mask_len a;
  rewrite (MU.pts_to_maybe_uninit (array_cell_ref a i) w)
       as (MU.pts_to_maybe_uninit (R.array_at_ghost a i) w);
  MU.return_array_at_maybe a i;
  let y : array_spec t = hide (array_spec_set s i w);
  to_seq_borrow s i;
  to_seq_set s i w;
  A.mask_vext a (to_seq y);
  A.mask_mext a (to_mask y);
  fold (array_pts_to a 1.0R y);
}

// Borrow the cell an arrayptr `x` points at, out of its live parent array `y`.
// The runtime carve is the same mask reshape as `array_borrow_cell`, only keyed
// on the arrayptr's own offset (`arrayptr_off x y`) instead of an explicit
// index; producing the concrete cell pointer from `x` needs the same concrete
// pointer-arithmetic primitive the rest of the arrayptr layer is still waiting
// on (cf. `array_to_arrayptr`, `arrayptr_read`, `arrayptr_diff`), so this is
// admitted like its siblings. The spec is the sound borrow contract PAL relies
// on.
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
{
  admit ()
}

// Return a cell borrowed with `arrayptr_borrow_cell` (dual of the above). Unlike
// its executable borrow counterpart, this is a ghost lemma: it needs no runtime
// pointer, so it is *not* admitted. It simply delegates to `array_return_cell` at
// index `arrayptr_off x y` (a nat by the `#s` refinement); the pure
// `arrayptr_pts_to x y` witness is untouched and frames through.
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
{
  array_return_cell y #(arrayptr_off x y) #w #s;
}
