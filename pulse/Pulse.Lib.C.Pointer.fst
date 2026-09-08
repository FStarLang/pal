module Pulse.Lib.C.Pointer

open Pulse.Lib.C.CoreRef
module I = FStar.Int
module U = FStar.UInt
module M = FStar.Math.Lemmas

#set-options "--z3rlimit 10"

(* The width here is only that of the requested mathematical integer view;
   it is not a pointer width. Narrowing deliberately loses information. *)
let unsigned_view width p =
  let x = core_address p in
  let modulus = pow2 width in
  if 0 <= x && x < modulus then M.small_mod x modulus;
  if -modulus <= x && x < 0 then (
    M.lemma_mod_plus x 1 modulus;
    M.small_mod (x + modulus) modulus
  );
  x % modulus

let signed_view width p =
  let u = unsigned_view width p in
  let x = core_address p in
  if I.fits x width then (
    assert (u == I.to_uint #width x);
    I.to_uint_injective #width x
  );
  I.from_uint #width u

let null_address (p: core_ref)
  : Lemma
      (requires p == core_null)
      (ensures core_address p == 0)
      [SMTPat (core_address p)]
  = let _ = integer_to_core 0 in ()
