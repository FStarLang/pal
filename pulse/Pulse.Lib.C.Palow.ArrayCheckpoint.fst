module Pulse.Lib.C.Palow.ArrayCheckpoint
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
module Q = FStar.Seq
module Z = FStar.SizeT

// The first k of the n elements are written. Opaque: a transparent quantifier
// here would be instantiated afresh in every later query of the function, for
// every checkpoint still in scope.
[@@"opaque_to_smt"]
let prefix (#t:Type0) (xs:Q.seq (option t)) (n k:nat) : prop =
  Q.length xs == n /\ k <= n /\
  (forall (j:nat). j < k ==> Some? (Q.index xs j))

// What a seal needs of the array before the write: its length, and that the
// elements before this one are already written.
let ready (#t:Type0) (xs:Q.seq (option t)) (n k:nat) : prop =
  Q.length xs == n /\ (k > 0 ==> prefix xs n k)

let advance (#t:Type0) (xs:Q.seq (option t)) (n k:nat{k < n /\ ready xs n k}) (v:t)
  : Lemma (Q.length (Q.upd xs k (Some v)) == n /\
           prefix (Q.upd xs k (Some v)) n (k + 1) /\
           (k + 1 == n ==> (forall (j:nat). j < n ==> Some? (Q.index (Q.upd xs k (Some v)) j))))
  = reveal_opaque (`%prefix) (prefix #t)

// The split, physical write and unfocus must already have produced this very
// update. The seal names the contents afterwards and keeps only what later
// steps use: the length, the written prefix, and, after the last element,
// that every element is written. It does not relate the new contents to the
// old ones: that equation would hand the solver the chain of every earlier
// update, in every later query.
ghost fn seal (#t:Type0) (repr:t -> bytes -> prop) (a:ptr) (es al:Z.t)
  (n:nat) (i:Z.t{Z.v i < n}) (xs:erased (Q.seq (option t)){ready (reveal xs) n (Z.v i)})
  (#v:erased t)
  requires array_pts_to (maybe_repr repr (Z.v es)) (Z.v es) (Z.v al) a 1.0R
    (Q.upd (reveal xs) (Z.v i) (Some (reveal v)))
  ensures exists* ys. array_pts_to (maybe_repr repr (Z.v es)) (Z.v es) (Z.v al) a 1.0R ys **
    pure (Q.length ys == n /\ prefix ys n (Z.v i + 1) /\
          (Z.v i + 1 == n ==> (forall (j:nat). j < n ==> Some? (Q.index ys j))))
{
  advance (reveal xs) n (Z.v i) (reveal v);
  assert pure (prefix (Q.upd (reveal xs) (Z.v i) (Some (reveal v))) n (Z.v i + 1));
}
