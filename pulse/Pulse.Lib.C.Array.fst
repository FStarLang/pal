module Pulse.Lib.C.Array
open Pulse
open Pulse.Lib.C.Inhabited
module A = Pulse.Lib.Array
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

let array_spec_of_list xs =
  Seq.init (List.length xs) fun i -> Val (List.Tot.index xs i)

let array_spec_of_list_full_len xs = ()

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
  array_spec_of_list_full_len xs;
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

fn calloc_array u#a (#a:Type u#a) {| small_type u#a |} {| has_zero_default a |} (sz:SZ.t)
  returns r : array a
  ensures freeable_array r
  ensures exists* y. array_pts_to r 1.0R y ** pure (y == array_spec_zeroed a (SizeT.v sz) zero_default)
{
  let r = A.alloc (zero_default #a) sz;
  A.to_mask r;
  mask_mext r (to_mask (array_spec_zeroed a (SZ.v sz) zero_default));
  mask_vext r (to_seq (array_spec_zeroed a (SZ.v sz) zero_default));
  fold array_pts_to r 1.0R (array_spec_zeroed a (SZ.v sz) zero_default);
  fold freeable_array r;
  r
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

let length #t (a: array t) : GTot nat = A.length a
let base_of #t (a: array t) : base_t = A.base_of a
let offset_of #t (a: array t) : GTot nat = A.offset_of a

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

let arrayptr_shift #t x n #y =
  admit ()
  // Stuck: need a concrete operation to shift the pointer.

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

let arrayptr_diff #t x z = admit ()
// Stuck: need a concrete primitive to compute pointer difference.

let arrayptr_eq #t x z = admit ()
// Stuck: need a concrete pointer equality primitive.

let arrayptr_lte #t x z = admit ()
// Stuck: need a concrete pointer comparison primitive.

let arrayptr_lt #t x z = admit ()
// Stuck: need a concrete pointer comparison primitive.
