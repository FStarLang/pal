module Pulse.Lib.C.FuncPtr
#lang-pulse
open Pulse
open Pulse.Lib.C.Inhabited

(* ============================================================================
   Function-pointer model: axioms vs. derived facts

   A C function pointer is modelled as an abstract type equipped with a validity
   relation to a Pulse spec. Validity carries a `div` boolean discriminating a
   pointer to a TOTAL Pulse function (`div = false`, callable via `call`) from
   one to a POSSIBLY-DIVERGENT function (`div = true`, callable via `call_div`).
   PAL emits every function as `divergent` unless it is `_total`, so most decayed
   pointers are `div = true` (`of_fn_div`); `_total` functions decay at
   `div = false` (`of_fn`). The primitives below fall into two groups.

   AXIOMS (abstract `val`s with no body -- the trusted core, taken on faith):
     - func_ptr        : the abstract pointer type
     - valid           : the (pure) "pointer meets this spec (at divergence `div`)"
     - null            : the null pointer
     - of_fn           : reflect a concrete TOTAL Pulse function as a pointer
     - of_fn_valid     : `of_fn` is valid at its own spec, `div = false`
     - of_fn_div       : reflect a concrete DIVERGENT Pulse function as a pointer
     - of_fn_div_valid : `of_fn_div` is valid at its own spec, `div = true`
     - weaken          : move validity across a spec weakening and/or total->div
     - call            : indirect call of a TOTAL pointer (returns `stt`)
     - call_div        : indirect call of a DIVERGENT pointer (returns `stt_div`)
     - is_null         : decidable null test

   DERIVABLE (defined/proven from the axioms above -- nothing new is assumed):
     - is_valid      : `let`-definition, `pure (valid ..)`
     - drop_is_valid : proven `ghost fn` (just `unfold`s `is_valid` to `emp`)
     - valid_cast    : proven `ghost fn` (unfold/fold across a value equality)
   ============================================================================ *)

(* Abstract C function pointer: `a` is the (tupled) argument type, `b` the return
   type. Inhabited by `null`, so it can be stored in refs, fields, arrays, globals. *)
val func_ptr (a: Type0) (b: Type0) : Type0

(* `valid f div pre post`: the pointer `f` meets the spec `(pre, post)`; `div`
   records whether `f` may diverge. A pure prop, so `is_valid` is a persistent
   fact threadable without touching the heap. *)
val valid (#a #b: Type0) (f: func_ptr a b) (div: bool) (pre: a -> slprop) (post: a -> b -> slprop) : prop
let is_valid (#a #b: Type0) ([@@@mkey] f: func_ptr a b) (div: bool) (pre: a -> slprop) (post: a -> b -> slprop) : slprop = pure (valid f div pre post)

(* Drop a surplus `is_valid` back to `emp` (it is persistent). Proven, not
   axiomatized: `is_valid` unfolds to `pure`. `f` is `[@@@mkey]`, so the resource in
   context is matched by the pointer and `div`/`pre`/`post` are inferred. *)
ghost fn drop_is_valid (#a #b: Type0) (#div: bool) (f: func_ptr a b) (pre: a -> slprop) (post: a -> b -> slprop)
  requires is_valid f div pre post
  ensures emp
{
  unfold (is_valid f div pre post);
}

(* Move `is_valid` across a provable value equality `f == g`. Needed to call
   through a pointer read back from an array slot, where the read value is only
   provably (not syntactically) equal to the stored `of_fn ..`. *)
ghost fn valid_cast (#a #b: Type0) (#div: bool) (#pre: a -> slprop) (#post: a -> b -> slprop)
  (f g: func_ptr a b)
  requires is_valid f div pre post ** pure (f == g)
  ensures is_valid g div pre post
{
  unfold (is_valid f div pre post);
  fold (is_valid g div pre post);
}


(* The null function pointer. *)
val null (a b: Type0) : func_ptr a b

(* Reflect a concrete TOTAL Pulse function as a pointer. pre/post are explicit to
   avoid higher-order-unification failures. *)
val of_fn (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: (x:a -> stt b (pre x) (fun r -> post x r))) : func_ptr a b

(* Ghost step yielding `is_valid (of_fn ..) false ..`: `of_fn` is valid, at its own
   spec, as a total pointer. *)
val of_fn_valid (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: (x:a -> stt b (pre x) (fun r -> post x r)))
  : stt_ghost unit emp_inames emp (fun _ -> is_valid (of_fn pre post f) false pre post)

(* Reflect a concrete POSSIBLY-DIVERGENT Pulse function as a pointer. *)
val of_fn_div (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: (x:a -> stt_div b (pre x) (fun r -> post x r))) : func_ptr a b

(* Ghost step yielding `is_valid (of_fn_div ..) true ..`: `of_fn_div` is valid, at
   its own spec, as a divergent pointer. *)
val of_fn_div_valid (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: (x:a -> stt_div b (pre x) (fun r -> post x r)))
  : stt_ghost unit emp_inames emp (fun _ -> is_valid (of_fn_div pre post f) true pre post)

(* Transfer validity across a spec weakening and/or a divergence relaxation: given
   ghost coercions from the new pre to the old pre and from the old post to the new
   post, `is_valid` moves from `(div, pre, post)` to `(div', pre', post')`. The
   refinement `div ==> div'` permits total->divergent (a total pointer is trivially
   a valid divergent one) but forbids the unsound divergent->total. *)
val weaken (#a #b: Type0) (f: func_ptr a b)
  (div: bool) (div': bool { div ==> div' })
  (pre: a -> slprop) (post: a -> b -> slprop)
  (pre': a -> slprop) (post': a -> b -> slprop)
  (wpre:  (x:a -> stt_ghost unit emp_inames (pre' x) (fun _ -> pre x)))
  (wpost: (x:a -> y:b -> stt_ghost unit emp_inames (post x y) (fun _ -> post' x y)))
  : stt_ghost unit emp_inames
      (is_valid f div pre post)
      (fun _ -> (is_valid f div' pre' post'))

(* Indirect call of a TOTAL pointer: consume `is_valid f false pre post ** pre x`.
   pre/post are explicit (SMT will not solve the higher-order metavariables). The
   post also RETURNS `is_valid f false pre post` (validity is persistent), so a
   caller can thread it across the call; callers that do not need it drop the
   surplus. Returns `stt` -- usable from any (total or divergent) context. *)
val call (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: func_ptr a b)  (x: a)
  : stt b (is_valid f false pre post  ** pre x) (fun r -> is_valid f false pre post ** post x r)

(* Indirect call of a POSSIBLY-DIVERGENT pointer: as `call`, but keyed on
   `is_valid f true ..` and returning `stt_div`, so it lives in the divergent
   effect (and can only be used from a `divergent` body). *)
val call_div (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: func_ptr a b)  (x: a)
  : stt_div b (is_valid f true pre post  ** pre x) (fun r -> is_valid f true pre post ** post x r)

(* Decidable null test, for C `if (fp)` / `fp == NULL`. *)
val is_null (#a #b: Type0) (f: func_ptr a b) : (r: bool { r <==> f == null a b })

instance inhabited_func_ptr (a b: Type0) : inhabited (func_ptr a b) = { witness = null a b }
instance has_zero_default_func_ptr (a b: Type0) : has_zero_default (func_ptr a b) = { zero_default = null a b }

(* `has_is_null` instance so a func-pointer parameter can be marked `_nullable`. *)
instance has_is_null_func_ptr (a b: Type0) : Pulse.Lib.C.Nullable.has_is_null (func_ptr a b) =
  { test_null = (fun f -> is_null f) }
