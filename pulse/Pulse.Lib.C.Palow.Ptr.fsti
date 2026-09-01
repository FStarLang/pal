module Pulse.Lib.C.Palow.Ptr

(* ---------------------------------------------------------------------------
   Palow layer 0: pointers.

   Following PNVI-ae-udi, a pointer is a concrete address together with a
   provenance tag naming the allocation it was derived from. Both projections
   are ghost: running code may compare pointers and offset them, but may not
   observe an address as an integer without going through the (as yet
   unimplemented, see milestone 7 in `palow.md`) exposure discipline.

   This interface is axiomatized: there is no `.fst`. It describes the machine,
   not a program.
   --------------------------------------------------------------------------- *)

open Pulse.Lib.C.Palow.Bytes
module SZ = FStar.SizeT

val ptr : Type0

val null : ptr

val ptr_eq (a1 a2: ptr) : (b:bool { b <==> a1 == a2 })

let is_null (a: ptr) : bool = ptr_eq a null

(* The address a pointer denotes, and the allocation it was derived from.
   `None` is the empty provenance: a pointer not derived from any allocation
   (`null`, or one manufactured from an integer without exposure). *)
val addr_of (a: ptr) : GTot nat
val prov_of (a: ptr) : GTot prov

(* A pointer is determined by its address and its provenance. Note that this
   makes pointer equality *provenance-sensitive*: two pointers with the same
   address but different provenance are different pointers, which is exactly
   what distinguishes PNVI from a flat address model. *)
val ptr_ext (a1 a2: ptr)
  : Lemma (requires addr_of a1 == addr_of a2 /\ prov_of a1 == prov_of a2)
          (ensures  a1 == a2)

val null_addr : squash (addr_of null == 0 /\ prov_of null == None)

(* Byte offset. Provenance-preserving, as required for interior pointers of an
   allocation to remain usable -- this is what lets a pool allocator hand out
   pointers into a block it obtained from `malloc`.

   Known deviation from PNVI: `( +! )` is total, so forming an out-of-bounds
   pointer is not itself an error here; only *accessing* out of bounds is,
   because `mem_pts_to` is only ever available for in-bounds ranges. This is
   strictly more permissive than ISO C, and is recorded as such in `palow.md`. *)
val ( +! ) (a: ptr) (n: SZ.t) : ptr

val addr_of_add (a: ptr) (n: SZ.t)
  : Lemma (addr_of (a +! n) == addr_of a + SZ.v n /\
           prov_of (a +! n) == prov_of a)
          [SMTPat (addr_of (a +! n))]

val prov_of_add (a: ptr) (n: SZ.t)
  : Lemma (prov_of (a +! n) == prov_of a)
          [SMTPat (prov_of (a +! n))]

(* Offsetting by zero is the identity, and offsets compose. Both follow from
   `ptr_ext` but are stated here with patterns because every aggregate
   split/join proof needs them. *)
val add_zero (a: ptr)
  : Lemma (a +! 0sz == a)
          [SMTPat (a +! 0sz)]

val add_add (a: ptr) (m n: SZ.t)
  : Lemma (requires SZ.fits (SZ.v m + SZ.v n))
          (ensures  (a +! m) +! n == a +! SZ.add m n)
          [SMTPat ((a +! m) +! n)]

(* Ranges of addresses. `disjoint_ranges` is what `mem_pts_to_disjoint` returns:
   it is stated on addresses rather than on allocations because it is also what
   client code needs in order to conclude that two objects do not overlap. *)
let in_range (a: ptr) (n: nat) (x: nat) : prop =
  addr_of a <= x /\ x < addr_of a + n

let disjoint_ranges (a1: ptr) (n1: nat) (a2: ptr) (n2: nat) : prop =
  addr_of a1 + n1 <= addr_of a2 \/ addr_of a2 + n2 <= addr_of a1
