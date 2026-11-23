module Pulse.Lib.C.Palow.ArrayCheckpoint
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
module Q = FStar.Seq
module Z = FStar.SizeT

let prefix (#t:Type0) (xs:Q.seq (option t)) (n k:nat) : prop =
  Q.length xs == n /\ k <= n /\
  (forall (j:nat). j < k ==> Some? (Q.index xs j))

let advance (#t:Type0) (xs:Q.seq (option t)) (n k:nat{k < n /\ prefix xs n k}) (v:t)
  : Lemma (prefix (Q.upd xs k (Some v)) n (k+1)) = ()

// The split, physical write and unfocus must already have produced this very
// update. Name its snapshot without expanding eight copies of the old value.
ghost fn seal (#t:Type0) (repr:t -> bytes -> prop) (a:ptr) (es al:Z.t)
  (n:nat) (i:Z.t{Z.v i < n}) (xs:erased (Q.seq (option t)){prefix (reveal xs) n (Z.v i)})
  (#v:erased t)
  requires array_pts_to (maybe_repr repr (Z.v es)) (Z.v es) (Z.v al) a 1.0R
    (Q.upd (reveal xs) (Z.v i) (Some (reveal v)))
  ensures exists* ys. array_pts_to (maybe_repr repr (Z.v es)) (Z.v es) (Z.v al) a 1.0R ys **
    pure (prefix ys n (Z.v i + 1) /\ Q.equal ys (Q.upd (reveal xs) (Z.v i) (Some (reveal v))))
{
  advance (reveal xs) n (Z.v i) (reveal v);
}
