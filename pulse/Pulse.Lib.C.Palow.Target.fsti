module Pulse.Lib.C.Palow.Target

(* ---------------------------------------------------------------------------
   The target machine, left abstract.

   The library is proved for every target at once: nothing here says what the
   target is, so nothing that depends on it can be proved from the library
   alone. A generated module that is translated for one concrete target states
   which one it is with a top-level `assume` in its implementation (never in
   its interface, so the assumption does not reach the modules that use it);
   a module translated for no particular target states nothing, and what it
   proves holds on all of them. See `palow.md`.
   --------------------------------------------------------------------------- *)

(* Whether a scalar's object representation puts its least significant byte at
   the lowest address. *)
val little_endian : bool

(* Whether a pointer is eight bytes wide (LP64, LLP64) rather than four
   (ILP32). `size_t`, `ptrdiff_t` and `uintptr_t` are pointer-sized on every
   target Palow supports, so this fixes their width too. *)
val ptr_64 : bool

let ptr_bytes : n:pos { n == 4 \/ n == 8 } = if ptr_64 then 8 else 4

(* One past the largest address, and one past the largest `size_t`. Spelled as
   a case split rather than `pow2 (8 * ptr_bytes)` so that, once a generated
   module has fixed `ptr_64`, it is literally the `pow2 64` (or `pow2 32`) the
   machine integer types are refined with. *)
let addr_limit : pos = if ptr_64 then pow2 64 else pow2 32

let addr_limit_pow2 () : Lemma (addr_limit == pow2 (8 * ptr_bytes)) = ()

(* A C alignment divides `pow2 32`, so it divides `addr_limit` on every target:
   which is all that reducing an address modulo `addr_limit` needs in order to
   preserve alignment. Stating side conditions on `pow2 32` keeps them closed
   numerals that do not mention the target. *)
let addr_limit_divisible (m: pos)
  : Lemma (requires pow2 32 % m == 0) (ensures addr_limit % m == 0)
  = if ptr_64 then begin
      FStar.Math.Lemmas.pow2_plus 32 32;
      FStar.Math.Lemmas.lemma_div_exact (pow2 32) m;
      FStar.Math.Lemmas.paren_mul_right (pow2 32 / m) m (pow2 32);
      FStar.Math.Lemmas.swap_mul m (pow2 32);
      FStar.Math.Lemmas.paren_mul_right (pow2 32 / m) (pow2 32) m;
      FStar.Math.Lemmas.multiple_modulo_lemma ((pow2 32 / m) * pow2 32) m
    end

(* `_Alignof(max_align_t)`: the strictest fundamental alignment, and what
   `malloc` guarantees (C11 7.22.3p1). 16 on x86-64 and AArch64 Linux, 8 on
   32-bit MIPS and ARM. At least `_Alignof(long long)`, so never below 8. *)
val max_align : n:FStar.SizeT.t {
  let v = FStar.SizeT.v n in v == 8 \/ v == 16 \/ v == 32 }
