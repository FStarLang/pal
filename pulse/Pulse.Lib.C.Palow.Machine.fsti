module Pulse.Lib.C.Palow.Machine

(* The existing convenience operations are implementations over the indexed
   machine interface. Loads preserve actual metadata; stores establish only
   their lvalue type and never alter immutable origin. Character stores do
   not relabel. Pointer descriptors currently use coarse SPtr: exact pointee
   type compatibility is not represented.

   Indexed operations below use Effective.Value.value/storage. read_at keeps
   e; write_at and write_uninit_at return store_index e ct. write_existing
   keeps e only with Some metadata everywhere and current readability.
   initialize_at consumes opaque prepared ownership and returns its actual
   mutable index; initialize is the existential convenience wrapper.

   mem_stack_alloc takes an erased nominal descriptor and returns its exact
   declared index. Convenience scalar stack allocation hides that index;
   clients needing allocation/type evidence must retain indexed ownership.
   Stack destruction retains the pre-existing emitter-managed lifetime
   discipline; this migration does not add stack lifetime tokens. *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Float
open Pulse.Lib.C.Palow.CTypes

module ET = Pulse.Lib.C.Palow.Etype
module EM = Pulse.Lib.C.Palow.Effective.Machine
module V = Pulse.Lib.C.Palow.Effective.Value
module E = Pulse.Lib.C.Palow.Effective
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

fn uint32_t_read (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves uint32_t_pts_to a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)

fn uint32_t_write (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures  uint32_t_pts_to a 1.0R y

fn uint32_t_write_uninit (a: ptr) (y: U32.t)
  requires uint32_t_pts_to_uninit a
  ensures  uint32_t_pts_to a 1.0R y

fn uint8_t_read (a: ptr) (#p: perm) (#x: erased U8.t)
  preserves uint8_t_pts_to a p x
  returns  y : U8.t
  ensures  rewrites_to y (reveal x)

fn uint8_t_write (a: ptr) (y: U8.t) (#x: erased U8.t)
  requires uint8_t_pts_to a 1.0R x
  ensures  uint8_t_pts_to a 1.0R y

fn ptr_read (a: ptr) (#p: perm) (#x: erased ptr)
  preserves ptr_pts_to a p x
  returns  y : ptr
  ensures  rewrites_to y (reveal x)

fn ptr_write (a: ptr) (y: ptr) (#x: erased ptr)
  requires ptr_pts_to a 1.0R x
  ensures  ptr_pts_to a 1.0R y

fn uint32_t_stack_alloc ()
  returns  a : ptr
  ensures  uint32_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint32_t_ctype true))

fn uint32_t_stack_free (a: ptr)
  requires uint32_t_pts_to_uninit a

fn ptr_write_uninit (a: ptr) (y: ptr)
  requires ptr_pts_to_uninit a
  ensures  ptr_pts_to a 1.0R y

fn ptr_stack_alloc ()
  returns  a : ptr
  ensures  ptr_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of ptr_ctype true))

fn ptr_stack_free (a: ptr)
  requires ptr_pts_to_uninit a

fn bool_t_read (a: ptr) (#p: perm) (#x: erased bool)
  preserves bool_t_pts_to a p x
  returns  y : bool
  ensures  rewrites_to y (reveal x)

fn bool_t_write (a: ptr) (y: bool) (#x: erased bool)
  requires bool_t_pts_to a 1.0R x
  ensures  bool_t_pts_to a 1.0R y

fn bool_t_write_uninit (a: ptr) (y: bool)
  requires bool_t_pts_to_uninit a
  ensures  bool_t_pts_to a 1.0R y

fn bool_t_stack_alloc ()
  returns  a : ptr
  ensures  bool_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of bool_t_ctype true))

fn bool_t_stack_free (a: ptr)
  requires bool_t_pts_to_uninit a

fn int8_t_read (a: ptr) (#p: perm) (#x: erased I8.t)
  preserves int8_t_pts_to a p x
  returns  y : I8.t
  ensures  rewrites_to y (reveal x)

fn int8_t_write (a: ptr) (y: I8.t) (#x: erased I8.t)
  requires int8_t_pts_to a 1.0R x
  ensures  int8_t_pts_to a 1.0R y

fn int8_t_write_uninit (a: ptr) (y: I8.t)
  requires int8_t_pts_to_uninit a
  ensures  int8_t_pts_to a 1.0R y

fn int8_t_stack_alloc ()
  returns  a : ptr
  ensures  int8_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int8_t_ctype true))

fn int8_t_stack_free (a: ptr)
  requires int8_t_pts_to_uninit a

fn int16_t_read (a: ptr) (#p: perm) (#x: erased I16.t)
  preserves int16_t_pts_to a p x
  returns  y : I16.t
  ensures  rewrites_to y (reveal x)

fn int16_t_write (a: ptr) (y: I16.t) (#x: erased I16.t)
  requires int16_t_pts_to a 1.0R x
  ensures  int16_t_pts_to a 1.0R y

fn int16_t_write_uninit (a: ptr) (y: I16.t)
  requires int16_t_pts_to_uninit a
  ensures  int16_t_pts_to a 1.0R y

fn int16_t_stack_alloc ()
  returns  a : ptr
  ensures  int16_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int16_t_ctype true))

fn int16_t_stack_free (a: ptr)
  requires int16_t_pts_to_uninit a

fn int32_t_read (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves int32_t_pts_to a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)

fn int32_t_write (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires int32_t_pts_to a 1.0R x
  ensures  int32_t_pts_to a 1.0R y

fn int32_t_write_uninit (a: ptr) (y: I32.t)
  requires int32_t_pts_to_uninit a
  ensures  int32_t_pts_to a 1.0R y

fn int32_t_stack_alloc ()
  returns  a : ptr
  ensures  int32_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int32_t_ctype true))

fn int32_t_stack_free (a: ptr)
  requires int32_t_pts_to_uninit a

fn int64_t_read (a: ptr) (#p: perm) (#x: erased I64.t)
  preserves int64_t_pts_to a p x
  returns  y : I64.t
  ensures  rewrites_to y (reveal x)

fn int64_t_write (a: ptr) (y: I64.t) (#x: erased I64.t)
  requires int64_t_pts_to a 1.0R x
  ensures  int64_t_pts_to a 1.0R y

fn int64_t_write_uninit (a: ptr) (y: I64.t)
  requires int64_t_pts_to_uninit a
  ensures  int64_t_pts_to a 1.0R y

fn int64_t_stack_alloc ()
  returns  a : ptr
  ensures  int64_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int64_t_ctype true))

fn int64_t_stack_free (a: ptr)
  requires int64_t_pts_to_uninit a

fn uint8_t_write_uninit (a: ptr) (y: U8.t)
  requires uint8_t_pts_to_uninit a
  ensures  uint8_t_pts_to a 1.0R y

fn uint8_t_stack_alloc ()
  returns  a : ptr
  ensures  uint8_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint8_t_ctype true))

fn uint8_t_stack_free (a: ptr)
  requires uint8_t_pts_to_uninit a

fn uint16_t_read (a: ptr) (#p: perm) (#x: erased U16.t)
  preserves uint16_t_pts_to a p x
  returns  y : U16.t
  ensures  rewrites_to y (reveal x)

fn uint16_t_write (a: ptr) (y: U16.t) (#x: erased U16.t)
  requires uint16_t_pts_to a 1.0R x
  ensures  uint16_t_pts_to a 1.0R y

fn uint16_t_write_uninit (a: ptr) (y: U16.t)
  requires uint16_t_pts_to_uninit a
  ensures  uint16_t_pts_to a 1.0R y

fn uint16_t_stack_alloc ()
  returns  a : ptr
  ensures  uint16_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint16_t_ctype true))

fn uint16_t_stack_free (a: ptr)
  requires uint16_t_pts_to_uninit a

fn uint64_t_read (a: ptr) (#p: perm) (#x: erased U64.t)
  preserves uint64_t_pts_to a p x
  returns  y : U64.t
  ensures  rewrites_to y (reveal x)

fn uint64_t_write (a: ptr) (y: U64.t) (#x: erased U64.t)
  requires uint64_t_pts_to a 1.0R x
  ensures  uint64_t_pts_to a 1.0R y

fn uint64_t_write_uninit (a: ptr) (y: U64.t)
  requires uint64_t_pts_to_uninit a
  ensures  uint64_t_pts_to a 1.0R y

fn uint64_t_stack_alloc ()
  returns  a : ptr
  ensures  uint64_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint64_t_ctype true))

fn uint64_t_stack_free (a: ptr)
  requires uint64_t_pts_to_uninit a

fn size_t_read (a: ptr) (#p: perm) (#x: erased SZ.t)
  preserves size_t_pts_to a p x
  returns  y : SZ.t
  ensures  rewrites_to y (reveal x)

fn size_t_write (a: ptr) (y: SZ.t) (#x: erased SZ.t)
  requires size_t_pts_to a 1.0R x
  ensures  size_t_pts_to a 1.0R y

fn size_t_write_uninit (a: ptr) (y: SZ.t)
  requires size_t_pts_to_uninit a
  ensures  size_t_pts_to a 1.0R y

fn size_t_stack_alloc ()
  returns  a : ptr
  ensures  size_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of size_t_ctype true))

fn size_t_stack_free (a: ptr)
  requires size_t_pts_to_uninit a

fn float32_t_read (a: ptr) (#p: perm) (#x: erased float32)
  preserves float32_t_pts_to a p x
  returns  y : float32
  ensures  rewrites_to y (reveal x)

fn float32_t_write (a: ptr) (y: float32) (#x: erased float32)
  requires float32_t_pts_to a 1.0R x
  ensures  float32_t_pts_to a 1.0R y

fn float32_t_write_uninit (a: ptr) (y: float32)
  requires float32_t_pts_to_uninit a
  ensures  float32_t_pts_to a 1.0R y

fn float32_t_stack_alloc ()
  returns  a : ptr
  ensures  float32_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of float32_t_ctype true))

fn float32_t_stack_free (a: ptr)
  requires float32_t_pts_to_uninit a

fn float64_t_read (a: ptr) (#p: perm) (#x: erased float64)
  preserves float64_t_pts_to a p x
  returns  y : float64
  ensures  rewrites_to y (reveal x)

fn float64_t_write (a: ptr) (y: float64) (#x: erased float64)
  requires float64_t_pts_to a 1.0R x
  ensures  float64_t_pts_to a 1.0R y

fn float64_t_write_uninit (a: ptr) (y: float64)
  requires float64_t_pts_to_uninit a
  ensures  float64_t_pts_to a 1.0R y

fn float64_t_stack_alloc ()
  returns  a : ptr
  ensures  float64_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of float64_t_ctype true))

fn float64_t_stack_free (a: ptr)
  requires float64_t_pts_to_uninit a

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

fn memset_zero (dst: ptr) (n: SZ.t) (#bd: erased bytes) (#ed: ET.etypes)
  requires mem_pts_to_at dst 1.0R bd ed
  requires pure (len bd == SZ.v n /\ ET.elen ed == len bd)
  ensures mem_pts_to_at dst 1.0R (zeroed (SZ.v n)) ed

fn mem_stack_alloc (n: SZ.t) (ct: erased ET.ctype)
  requires pure (SZ.v n == ET.csize (reveal ct))
  returns a: ptr
  ensures mem_pts_to_at a 1.0R (uninit (SZ.v n)) (ET.etypes_of (reveal ct) true)
    ** pure (aligned a max_align /\ fixed_metadata a (ET.etypes_of (reveal ct) true))

fn mem_stack_free (a: ptr) (#b: erased bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e


fn uint32_t_read_at (a: ptr) (#p: perm) (#x: erased U32.t) (#e: ET.etypes)
  preserves V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a p x e
  returns y: U32.t
  ensures rewrites_to y (reveal x)

fn uint32_t_write_at (a: ptr) (y: U32.t) (#x: erased U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint32_t_ctype })
  requires V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R x e
  ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y (EM.store_index e uint32_t_ctype)

fn uint32_t_write_uninit_at (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint32_t_ctype })
  requires V.storage uint32_t_ctype uint32_t_alignof a e
  ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y (EM.store_index e uint32_t_ctype)

fn uint32_t_write_existing (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint32_t_ctype })
  requires V.storage uint32_t_ctype uint32_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y e

fn uint32_t_initialize_at (a: ptr) (y: U32.t)
  requires E.prepared a uint32_t_ctype
  requires pure (aligned a uint32_t_alignof)
  ensures exists* e. V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint32_t_ctype) ==> e == ET.etypes_of uint32_t_ctype false))

fn uint32_t_initialize (a: ptr) (y: U32.t)
  requires E.prepared a uint32_t_ctype
  requires pure (aligned a uint32_t_alignof)
  ensures uint32_t_pts_to a 1.0R y

fn uint8_t_read_at (a: ptr) (#p: perm) (#x: erased U8.t) (#e: ET.etypes)
  preserves V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a p x e
  returns y: U8.t
  ensures rewrites_to y (reveal x)

fn uint8_t_write_at (a: ptr) (y: U8.t) (#x: erased U8.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint8_t_ctype })
  requires V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R x e
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y (EM.store_index e uint8_t_ctype)

fn uint8_t_write_uninit_at (a: ptr) (y: U8.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint8_t_ctype })
  requires V.storage uint8_t_ctype uint8_t_alignof a e
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y (EM.store_index e uint8_t_ctype)

fn uint8_t_write_existing (a: ptr) (y: U8.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint8_t_ctype })
  requires V.storage uint8_t_ctype uint8_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y e

fn uint8_t_initialize_at (a: ptr) (y: U8.t)
  requires E.prepared a uint8_t_ctype
  requires pure (aligned a uint8_t_alignof)
  ensures exists* e. V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint8_t_ctype) ==> e == ET.etypes_of uint8_t_ctype false))

fn uint8_t_initialize (a: ptr) (y: U8.t)
  requires E.prepared a uint8_t_ctype
  requires pure (aligned a uint8_t_alignof)
  ensures uint8_t_pts_to a 1.0R y

fn ptr_read_at (a: ptr) (#p: perm) (#x: erased ptr) (#e: ET.etypes)
  preserves V.value ptr_ctype ptr_repr ptr_alignof a p x e
  returns y: ptr
  ensures rewrites_to y (reveal x)

fn ptr_write_at (a: ptr) (y: ptr) (#x: erased ptr)
    (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires V.value ptr_ctype ptr_repr ptr_alignof a 1.0R x e
  ensures V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y (EM.store_index e ptr_ctype)

fn ptr_write_uninit_at (a: ptr) (y: ptr)
    (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires V.storage ptr_ctype ptr_alignof a e
  ensures V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y (EM.store_index e ptr_ctype)

fn ptr_write_existing (a: ptr) (y: ptr)
    (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires V.storage ptr_ctype ptr_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y e

fn ptr_initialize_at (a: ptr) (y: ptr)
  requires E.prepared a ptr_ctype
  requires pure (aligned a ptr_alignof)
  ensures exists* e. V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type ptr_ctype) ==> e == ET.etypes_of ptr_ctype false))

fn ptr_initialize (a: ptr) (y: ptr)
  requires E.prepared a ptr_ctype
  requires pure (aligned a ptr_alignof)
  ensures ptr_pts_to a 1.0R y

fn bool_t_read_at (a: ptr) (#p: perm) (#x: erased bool) (#e: ET.etypes)
  preserves V.value bool_t_ctype bool_t_repr bool_t_alignof a p x e
  returns y: bool
  ensures rewrites_to y (reveal x)

fn bool_t_write_at (a: ptr) (y: bool) (#x: erased bool)
    (#e: ET.etypes { ET.elen e == ET.csize bool_t_ctype })
  requires V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R x e
  ensures V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y (EM.store_index e bool_t_ctype)

fn bool_t_write_uninit_at (a: ptr) (y: bool)
    (#e: ET.etypes { ET.elen e == ET.csize bool_t_ctype })
  requires V.storage bool_t_ctype bool_t_alignof a e
  ensures V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y (EM.store_index e bool_t_ctype)

fn bool_t_write_existing (a: ptr) (y: bool)
    (#e: ET.etypes { ET.elen e == ET.csize bool_t_ctype })
  requires V.storage bool_t_ctype bool_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y e

fn bool_t_initialize_at (a: ptr) (y: bool)
  requires E.prepared a bool_t_ctype
  requires pure (aligned a bool_t_alignof)
  ensures exists* e. V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type bool_t_ctype) ==> e == ET.etypes_of bool_t_ctype false))

fn bool_t_initialize (a: ptr) (y: bool)
  requires E.prepared a bool_t_ctype
  requires pure (aligned a bool_t_alignof)
  ensures bool_t_pts_to a 1.0R y

fn int8_t_read_at (a: ptr) (#p: perm) (#x: erased I8.t) (#e: ET.etypes)
  preserves V.value int8_t_ctype int8_t_repr int8_t_alignof a p x e
  returns y: I8.t
  ensures rewrites_to y (reveal x)

fn int8_t_write_at (a: ptr) (y: I8.t) (#x: erased I8.t)
    (#e: ET.etypes { ET.elen e == ET.csize int8_t_ctype })
  requires V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R x e
  ensures V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y (EM.store_index e int8_t_ctype)

fn int8_t_write_uninit_at (a: ptr) (y: I8.t)
    (#e: ET.etypes { ET.elen e == ET.csize int8_t_ctype })
  requires V.storage int8_t_ctype int8_t_alignof a e
  ensures V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y (EM.store_index e int8_t_ctype)

fn int8_t_write_existing (a: ptr) (y: I8.t)
    (#e: ET.etypes { ET.elen e == ET.csize int8_t_ctype })
  requires V.storage int8_t_ctype int8_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y e

fn int8_t_initialize_at (a: ptr) (y: I8.t)
  requires E.prepared a int8_t_ctype
  requires pure (aligned a int8_t_alignof)
  ensures exists* e. V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int8_t_ctype) ==> e == ET.etypes_of int8_t_ctype false))

fn int8_t_initialize (a: ptr) (y: I8.t)
  requires E.prepared a int8_t_ctype
  requires pure (aligned a int8_t_alignof)
  ensures int8_t_pts_to a 1.0R y

fn int16_t_read_at (a: ptr) (#p: perm) (#x: erased I16.t) (#e: ET.etypes)
  preserves V.value int16_t_ctype int16_t_repr int16_t_alignof a p x e
  returns y: I16.t
  ensures rewrites_to y (reveal x)

fn int16_t_write_at (a: ptr) (y: I16.t) (#x: erased I16.t)
    (#e: ET.etypes { ET.elen e == ET.csize int16_t_ctype })
  requires V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R x e
  ensures V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y (EM.store_index e int16_t_ctype)

fn int16_t_write_uninit_at (a: ptr) (y: I16.t)
    (#e: ET.etypes { ET.elen e == ET.csize int16_t_ctype })
  requires V.storage int16_t_ctype int16_t_alignof a e
  ensures V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y (EM.store_index e int16_t_ctype)

fn int16_t_write_existing (a: ptr) (y: I16.t)
    (#e: ET.etypes { ET.elen e == ET.csize int16_t_ctype })
  requires V.storage int16_t_ctype int16_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y e

fn int16_t_initialize_at (a: ptr) (y: I16.t)
  requires E.prepared a int16_t_ctype
  requires pure (aligned a int16_t_alignof)
  ensures exists* e. V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int16_t_ctype) ==> e == ET.etypes_of int16_t_ctype false))

fn int16_t_initialize (a: ptr) (y: I16.t)
  requires E.prepared a int16_t_ctype
  requires pure (aligned a int16_t_alignof)
  ensures int16_t_pts_to a 1.0R y

fn int32_t_read_at (a: ptr) (#p: perm) (#x: erased I32.t) (#e: ET.etypes)
  preserves V.value int32_t_ctype int32_t_repr int32_t_alignof a p x e
  returns y: I32.t
  ensures rewrites_to y (reveal x)

fn int32_t_write_at (a: ptr) (y: I32.t) (#x: erased I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize int32_t_ctype })
  requires V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R x e
  ensures V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y (EM.store_index e int32_t_ctype)

fn int32_t_write_uninit_at (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize int32_t_ctype })
  requires V.storage int32_t_ctype int32_t_alignof a e
  ensures V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y (EM.store_index e int32_t_ctype)

fn int32_t_write_existing (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize int32_t_ctype })
  requires V.storage int32_t_ctype int32_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y e

fn int32_t_initialize_at (a: ptr) (y: I32.t)
  requires E.prepared a int32_t_ctype
  requires pure (aligned a int32_t_alignof)
  ensures exists* e. V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int32_t_ctype) ==> e == ET.etypes_of int32_t_ctype false))

fn int32_t_initialize (a: ptr) (y: I32.t)
  requires E.prepared a int32_t_ctype
  requires pure (aligned a int32_t_alignof)
  ensures int32_t_pts_to a 1.0R y

fn int64_t_read_at (a: ptr) (#p: perm) (#x: erased I64.t) (#e: ET.etypes)
  preserves V.value int64_t_ctype int64_t_repr int64_t_alignof a p x e
  returns y: I64.t
  ensures rewrites_to y (reveal x)

fn int64_t_write_at (a: ptr) (y: I64.t) (#x: erased I64.t)
    (#e: ET.etypes { ET.elen e == ET.csize int64_t_ctype })
  requires V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R x e
  ensures V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y (EM.store_index e int64_t_ctype)

fn int64_t_write_uninit_at (a: ptr) (y: I64.t)
    (#e: ET.etypes { ET.elen e == ET.csize int64_t_ctype })
  requires V.storage int64_t_ctype int64_t_alignof a e
  ensures V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y (EM.store_index e int64_t_ctype)

fn int64_t_write_existing (a: ptr) (y: I64.t)
    (#e: ET.etypes { ET.elen e == ET.csize int64_t_ctype })
  requires V.storage int64_t_ctype int64_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y e

fn int64_t_initialize_at (a: ptr) (y: I64.t)
  requires E.prepared a int64_t_ctype
  requires pure (aligned a int64_t_alignof)
  ensures exists* e. V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int64_t_ctype) ==> e == ET.etypes_of int64_t_ctype false))

fn int64_t_initialize (a: ptr) (y: I64.t)
  requires E.prepared a int64_t_ctype
  requires pure (aligned a int64_t_alignof)
  ensures int64_t_pts_to a 1.0R y

fn uint16_t_read_at (a: ptr) (#p: perm) (#x: erased U16.t) (#e: ET.etypes)
  preserves V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a p x e
  returns y: U16.t
  ensures rewrites_to y (reveal x)

fn uint16_t_write_at (a: ptr) (y: U16.t) (#x: erased U16.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint16_t_ctype })
  requires V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R x e
  ensures V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y (EM.store_index e uint16_t_ctype)

fn uint16_t_write_uninit_at (a: ptr) (y: U16.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint16_t_ctype })
  requires V.storage uint16_t_ctype uint16_t_alignof a e
  ensures V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y (EM.store_index e uint16_t_ctype)

fn uint16_t_write_existing (a: ptr) (y: U16.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint16_t_ctype })
  requires V.storage uint16_t_ctype uint16_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y e

fn uint16_t_initialize_at (a: ptr) (y: U16.t)
  requires E.prepared a uint16_t_ctype
  requires pure (aligned a uint16_t_alignof)
  ensures exists* e. V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint16_t_ctype) ==> e == ET.etypes_of uint16_t_ctype false))

fn uint16_t_initialize (a: ptr) (y: U16.t)
  requires E.prepared a uint16_t_ctype
  requires pure (aligned a uint16_t_alignof)
  ensures uint16_t_pts_to a 1.0R y

fn uint64_t_read_at (a: ptr) (#p: perm) (#x: erased U64.t) (#e: ET.etypes)
  preserves V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a p x e
  returns y: U64.t
  ensures rewrites_to y (reveal x)

fn uint64_t_write_at (a: ptr) (y: U64.t) (#x: erased U64.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint64_t_ctype })
  requires V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R x e
  ensures V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y (EM.store_index e uint64_t_ctype)

fn uint64_t_write_uninit_at (a: ptr) (y: U64.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint64_t_ctype })
  requires V.storage uint64_t_ctype uint64_t_alignof a e
  ensures V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y (EM.store_index e uint64_t_ctype)

fn uint64_t_write_existing (a: ptr) (y: U64.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint64_t_ctype })
  requires V.storage uint64_t_ctype uint64_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y e

fn uint64_t_initialize_at (a: ptr) (y: U64.t)
  requires E.prepared a uint64_t_ctype
  requires pure (aligned a uint64_t_alignof)
  ensures exists* e. V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint64_t_ctype) ==> e == ET.etypes_of uint64_t_ctype false))

fn uint64_t_initialize (a: ptr) (y: U64.t)
  requires E.prepared a uint64_t_ctype
  requires pure (aligned a uint64_t_alignof)
  ensures uint64_t_pts_to a 1.0R y

fn size_t_read_at (a: ptr) (#p: perm) (#x: erased SZ.t) (#e: ET.etypes)
  preserves V.value size_t_ctype size_t_repr size_t_alignof a p x e
  returns y: SZ.t
  ensures rewrites_to y (reveal x)

fn size_t_write_at (a: ptr) (y: SZ.t) (#x: erased SZ.t)
    (#e: ET.etypes { ET.elen e == ET.csize size_t_ctype })
  requires V.value size_t_ctype size_t_repr size_t_alignof a 1.0R x e
  ensures V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y (EM.store_index e size_t_ctype)

fn size_t_write_uninit_at (a: ptr) (y: SZ.t)
    (#e: ET.etypes { ET.elen e == ET.csize size_t_ctype })
  requires V.storage size_t_ctype size_t_alignof a e
  ensures V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y (EM.store_index e size_t_ctype)

fn size_t_write_existing (a: ptr) (y: SZ.t)
    (#e: ET.etypes { ET.elen e == ET.csize size_t_ctype })
  requires V.storage size_t_ctype size_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y e

fn size_t_initialize_at (a: ptr) (y: SZ.t)
  requires E.prepared a size_t_ctype
  requires pure (aligned a size_t_alignof)
  ensures exists* e. V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type size_t_ctype) ==> e == ET.etypes_of size_t_ctype false))

fn size_t_initialize (a: ptr) (y: SZ.t)
  requires E.prepared a size_t_ctype
  requires pure (aligned a size_t_alignof)
  ensures size_t_pts_to a 1.0R y

fn float32_t_read_at (a: ptr) (#p: perm) (#x: erased float32) (#e: ET.etypes)
  preserves V.value float32_t_ctype float32_t_repr float32_t_alignof a p x e
  returns y: float32
  ensures rewrites_to y (reveal x)

fn float32_t_write_at (a: ptr) (y: float32) (#x: erased float32)
    (#e: ET.etypes { ET.elen e == ET.csize float32_t_ctype })
  requires V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R x e
  ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y (EM.store_index e float32_t_ctype)

fn float32_t_write_uninit_at (a: ptr) (y: float32)
    (#e: ET.etypes { ET.elen e == ET.csize float32_t_ctype })
  requires V.storage float32_t_ctype float32_t_alignof a e
  ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y (EM.store_index e float32_t_ctype)

fn float32_t_write_existing (a: ptr) (y: float32)
    (#e: ET.etypes { ET.elen e == ET.csize float32_t_ctype })
  requires V.storage float32_t_ctype float32_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y e

fn float32_t_initialize_at (a: ptr) (y: float32)
  requires E.prepared a float32_t_ctype
  requires pure (aligned a float32_t_alignof)
  ensures exists* e. V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type float32_t_ctype) ==> e == ET.etypes_of float32_t_ctype false))

fn float32_t_initialize (a: ptr) (y: float32)
  requires E.prepared a float32_t_ctype
  requires pure (aligned a float32_t_alignof)
  ensures float32_t_pts_to a 1.0R y

fn float64_t_read_at (a: ptr) (#p: perm) (#x: erased float64) (#e: ET.etypes)
  preserves V.value float64_t_ctype float64_t_repr float64_t_alignof a p x e
  returns y: float64
  ensures rewrites_to y (reveal x)

fn float64_t_write_at (a: ptr) (y: float64) (#x: erased float64)
    (#e: ET.etypes { ET.elen e == ET.csize float64_t_ctype })
  requires V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R x e
  ensures V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y (EM.store_index e float64_t_ctype)

fn float64_t_write_uninit_at (a: ptr) (y: float64)
    (#e: ET.etypes { ET.elen e == ET.csize float64_t_ctype })
  requires V.storage float64_t_ctype float64_t_alignof a e
  ensures V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y (EM.store_index e float64_t_ctype)

fn float64_t_write_existing (a: ptr) (y: float64)
    (#e: ET.etypes { ET.elen e == ET.csize float64_t_ctype })
  requires V.storage float64_t_ctype float64_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y e

fn float64_t_initialize_at (a: ptr) (y: float64)
  requires E.prepared a float64_t_ctype
  requires pure (aligned a float64_t_alignof)
  ensures exists* e. V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type float64_t_ctype) ==> e == ET.etypes_of float64_t_ctype false))

fn float64_t_initialize (a: ptr) (y: float64)
  requires E.prepared a float64_t_ctype
  requires pure (aligned a float64_t_alignof)
  ensures float64_t_pts_to a 1.0R y
