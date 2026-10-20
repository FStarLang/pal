module Pulse.Lib.C.Palow.Effective.Machine

(* Indexed machine operations. Their contracts change bytes only at actual
   stores/copies; ghost preparation alone never produces readable ownership.
   Machine's typed implementations delegate to this interface. *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Nullable
open Pulse.Lib.C.Palow.Effective

module ET = Pulse.Lib.C.Palow.Etype
module Alloc = Pulse.Lib.C.Palow.Alloc
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Relation = Pulse.Lib.C.Palow.Effective.Relation

let fresh_index (n: nat) : e:ET.etypes { ET.elen e == n } =
  Seq.create n None

let store_index (e: ET.etypes) (t: ET.ctype { ET.elen e == ET.csize t })
  : ET.etypes =
  if ET.character_type t then e else ET.store_etypes e t

fn malloc (n: SZ.t)
  returns a: ptr
  ensures pure (is_null a \/ allocated_region a (SZ.v n))
  ensures unless_null a
    (mem_pts_to_at a 1.0R (uninit (SZ.v n)) (fresh_index (SZ.v n))
     ** Alloc.freeable a n ** pure (aligned a max_align))

fn calloc (n: SZ.t)
  returns a: ptr
  ensures pure (is_null a \/ allocated_region a (SZ.v n))
  ensures unless_null a
    (mem_pts_to_at a 1.0R (zeroed (SZ.v n)) (fresh_index (SZ.v n))
     ** Alloc.freeable a n ** pure (aligned a max_align))

fn free (a: ptr) (#n: erased SZ.t) (#b: erased bytes) (#e: ET.etypes)
  requires Alloc.freeable a (reveal n) ** mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v n)

fn free_prepared (a: ptr) (t: erased ET.ctype) (#n: erased SZ.t)
  requires Alloc.freeable a (reveal n) ** prepared a (reveal t)
  requires pure (ET.csize (reveal t) == SZ.v n)

(* Destruction consumes the reservation without exposing its old bytes. The
   tail is the remainder of the same original allocation. *)
fn free_prepared_prefix (a: ptr) (n: erased SZ.t)
                        (t: erased (ct: ET.ctype { SZ.fits (ET.csize ct) }))
                        (#tail: erased bytes) (#e: ET.etypes)
  requires Alloc.freeable a (reveal n) ** prepared a (reveal t)
  requires mem_pts_to_at (a +! SZ.uint_to_t (ET.csize (reveal t))) 1.0R tail e
  requires pure (len tail + ET.csize (reveal t) == SZ.v n /\ ET.elen e == len tail)

(* The byte payload is the representation of a machine value. Representation
   validity and alignment are additionally required by the typed wrappers. *)
fn load (a: ptr) (t: erased ET.ctype)
        (#p: perm) (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (ET.elen e == len b /\ len b == ET.csize (reveal t) /\
                 ET.read_ok e (reveal t) /\ initialized b)
  returns r: bytes
  ensures rewrites_to r (reveal b)

fn store (a: ptr) (t: erased ET.ctype) (b: bytes)
         (#old: erased bytes)
         (#e: ET.etypes { ET.elen e == ET.csize (reveal t) })
  requires mem_pts_to_at a 1.0R old e
  requires pure (ET.elen e == len old /\ len b == len old /\
                 len b == ET.csize (reveal t) /\ initialized b /\
                 ET.read_ok e (reveal t))
  ensures mem_pts_to_at a 1.0R b (store_index e (reveal t))

(* A genuine whole typed store through a compatible aggregate/member view.
   Unlike ghost folding, this operation writes the payload before changing
   mutable labels; declared origin and compatible enclosing labels survive. *)
fn store_view (a: ptr) (t: erased ET.ctype) (b: bytes)
              (#old: erased bytes)
              (#e: ET.etypes { ET.elen e == ET.csize (reveal t) })
  requires mem_pts_to_at a 1.0R old e
  requires pure (len old == ET.elen e /\ len b == len old /\ initialized b /\
                 Relation.view_read_ok e (reveal t))
  ensures mem_pts_to_at a 1.0R b (Relation.store_view_index e (reveal t))

(* A character store preserves the old index. Noncharacter whole-object
   initialization establishes the explicitly reserved target type. *)
fn initialize (a: ptr) (t: erased ET.ctype) (b: bytes)
  requires prepared a (reveal t)
  requires pure (len b == ET.csize (reveal t) /\ initialized b)
  ensures exists* e. mem_pts_to_at a 1.0R b e
    ** pure (ET.read_ok e (reveal t) /\ ET.elen e == len b /\ mutable_index e /\
             (not (ET.character_type (reveal t)) ==>
               e == ET.etypes_of (reveal t) false))

fn memcpy (dst src: ptr) (n: SZ.t)
          (#p: perm) (#bs #bd: erased bytes) (#ed: ET.etypes)
          (#es: ET.etypes { ET.copy_complete_ok (ET.Ready ed) (ET.Ready es) })
  preserves mem_pts_to_at src p bs es
  requires mem_pts_to_at dst 1.0R bd ed
  requires pure (len bs == SZ.v n /\ len bd == SZ.v n /\
                 ET.elen es == len bs /\ ET.elen ed == len bd /\
                 ET.copy_complete_ok (ET.Ready ed) (ET.Ready es))
  ensures mem_pts_to_at dst 1.0R bs
    (ET.state_etypes (ET.complete_copy (ET.Ready ed) (ET.Ready es)))

fn memcpy_prepared (dst src: ptr) (n: SZ.t) (t: erased ET.ctype)
                   (#p: perm) (#bs: erased bytes) (#es: ET.etypes)
  preserves mem_pts_to_at src p bs es
  requires prepared dst (reveal t)
  requires pure (len bs == SZ.v n /\ ET.csize (reveal t) == SZ.v n /\
                 ET.established_type es (reveal t))
  ensures mem_pts_to_at dst 1.0R bs (ET.etypes_of (reveal t) false)

(* Character filling changes representation and initialization, not type. *)
fn memset_zero (dst: ptr) (n: SZ.t) (#bd: erased bytes) (#ed: ET.etypes)
  requires mem_pts_to_at dst 1.0R bd ed
  requires pure (len bd == SZ.v n /\ ET.elen ed == len bd)
  ensures mem_pts_to_at dst 1.0R (zeroed (SZ.v n)) ed

fn stack_alloc (n: SZ.t) (t: erased ET.ctype)
  requires pure (SZ.v n == ET.csize (reveal t))
  returns a: ptr
  ensures mem_pts_to_at a 1.0R (uninit (SZ.v n))
            (ET.etypes_of (reveal t) true)
    ** pure (aligned a max_align /\ fixed_metadata a (ET.etypes_of (reveal t) true))

fn stack_free (a: ptr) (#b: erased bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (ET.declared_destination e /\ ET.elen e == len b)
