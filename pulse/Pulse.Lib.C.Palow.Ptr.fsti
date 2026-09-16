module Pulse.Lib.C.Palow.Ptr

(* ---------------------------------------------------------------------------
   Palow layer 0: pointers.

   Following PNVI-ae-udi, a pointer is a concrete address together with a
   provenance tag naming the allocation it was derived from. Both projections
   are ghost: running code may compare pointers and offset them, but may not
   observe an address as an integer without going through the exposure
   discipline in `Pulse.Lib.C.Palow.Expose`.

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

(* Every address fits in a pointer-sized word. Stated as an explicit bound
   rather than as `SizeT.fits`, which is abstract, because the byte encoding of
   a *stored* pointer needs its address to round-trip through `ptr_sizeof`
   bytes. Like the rest of Palow this fixes an LP64 target; see `palow.md`. *)
val addr_bound (a: ptr)
  : Lemma (addr_of a < pow2 64)
          [SMTPat (addr_of a)]

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

(* Comparison, difference, and negative offset.

   ISO C defines `<`, `<=` and `-` on pointers only when both operands point
   into the same object (C11 6.5.6p9, 6.5.8p5). Palow compares and subtracts
   addresses instead, which is total and agrees with C wherever C says
   anything. This is the same known deviation as `( +! )`: forming a pointer is
   never an error here, only accessing through one. *)
val ptr_lt (a1 a2: ptr) : (b:bool { b <==> addr_of a1 < addr_of a2 })

val ptr_le (a1 a2: ptr) : (b:bool { b <==> addr_of a1 <= addr_of a2 })

(* The difference has to be representable, which is the caller's obligation in
   C too (C11 6.5.6p9). *)
val ptr_diff (a1: ptr) (a2: ptr { FStar.Int.size (addr_of a1 - addr_of a2) 64 })
  : (d: FStar.Int64.t { FStar.Int64.v d == addr_of a1 - addr_of a2 })

(* Total on the offsets that name an address at all: there is nothing below
   zero to point at. *)
val ( -! ) (a: ptr) (n: SZ.t { SZ.v n <= addr_of a }) : ptr

val addr_of_sub (a: ptr) (n: SZ.t { SZ.v n <= addr_of a })
  : Lemma (addr_of (a -! n) == addr_of a - SZ.v n /\
           prov_of (a -! n) == prov_of a)
          [SMTPat (addr_of (a -! n))]

(* The same offset backwards, total.

   `_container_of` -- Linux's `container_of`, MsQuic's
   `CXPLAT_CONTAINING_RECORD` -- recovers a pointer to an enclosing structure
   from a pointer to one of its fields. The offset it subtracts fits only
   because the field pointer really does point into such a structure, and that
   is a fact about the caller's ownership, not about the expression: nothing in
   `p` itself says it is `&s->f` rather than an arbitrary address. So the
   subtraction is total for the same reason `( +! )` is -- forming a pointer is
   never an error here, only accessing through one -- and coincides with
   `( -! )` wherever that is defined.

   What the offset is below that point is deliberately unspecified. A caller
   who knows the field pointer came from a structure knows it as
   `base +! offset`, and the round trip below is then exactly the
   `container (proj p) == p` the old model had to generate a lemma for. *)
val ( -? ) (a: ptr) (n: SZ.t) : ptr

val addr_of_sub_wrap (a: ptr) (n: SZ.t)
  : Lemma (requires SZ.v n <= addr_of a)
          (ensures addr_of (a -? n) == addr_of a - SZ.v n /\
                   prov_of (a -? n) == prov_of a)
          [SMTPat (addr_of (a -? n))]

(* Derivable from the two lemmas above by `ptr_ext` -- `addr_of (a +! n)` is at
   least `SZ.v n`, so the offset fits -- and stated here so that it fires
   without one. *)
val add_sub_wrap (a: ptr) (n: SZ.t)
  : Lemma ((a +! n) -? n == a)
          [SMTPat ((a +! n) -? n)]

(* Offset zero is the identity, which is what makes a `_container_of` on a
   first member pointer identity -- and, in particular, NULL-preserving. That
   matters: an intrusive list whose link sits at offset 0 is walked by
   recovering the node from the link, and a NULL terminator has to survive the
   recovery or the walk never ends. *)
val sub_wrap_zero (a: ptr)
  : Lemma (a -? 0sz == a)
          [SMTPat (a -? 0sz)]

(* Ranges of addresses. `disjoint_ranges` is what `mem_pts_to_disjoint` returns:
   it is stated on addresses rather than on allocations because it is also what
   client code needs in order to conclude that two objects do not overlap. *)
let in_range (a: ptr) (n: nat) (x: nat) : prop =
  addr_of a <= x /\ x < addr_of a + n

let disjoint_ranges (a1: ptr) (n1: nat) (a2: ptr) (n2: nat) : prop =
  addr_of a1 + n1 <= addr_of a2 \/ addr_of a2 + n2 <= addr_of a1
