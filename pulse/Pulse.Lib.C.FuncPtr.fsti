module Pulse.Lib.C.FuncPtr
#lang-pulse
open Pulse
open Pulse.Lib.C.Inhabited

(* Axiomatized C function pointer. `a` is the (tupled) argument type, `b` the
   return type. The type is abstract and inhabited by `null`, so it can be
   stored in refs, struct fields, arrays and globals. *)
val func_ptr (a: Type0) (b: Type0) : Type0

(* Validity: the pointer `f` meets the spec `(pre, post)`. A pure proposition,
   so it can be threaded as a `squash` fact without touching the heap. *)
val valid (#a #b: Type0) (f: func_ptr a b) (pre: a -> slprop) (post: a -> b -> slprop) : prop
let is_valid (#a #b: Type0) ([@@@mkey] f: func_ptr a b) (pre: a -> slprop) (post: a -> b -> slprop) : slprop = pure (valid f pre post)

(* `is_valid` is a pure, persistent fact, so a surplus copy can be discarded
   freely. This ghost step drops it back to `emp`. Because `call`'s postcondition
   now returns `is_valid f pre post`, a caller that calls through a pointer but
   does not itself export validity is left with a surplus `is_valid`; it discards
   it with a source-level `_ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _)`
   after the call (PAL does not insert this automatically). `f` is `[@@@mkey]`, so
   the surplus resource in context is matched by the pointer and `pre`/`post` are
   inferred. It is *proven* (not axiomatized): `is_valid` unfolds to `pure`, which
   `elim_pure` discharges. *)
ghost fn drop_is_valid (#a #b: Type0) (f: func_ptr a b) (pre: a -> slprop) (post: a -> b -> slprop)
  requires is_valid f pre post
  ensures emp
{
  unfold (is_valid f pre post);
}

(* The null function pointer. *)
val null (a b: Type0) : func_ptr a b

(* Reflect a concrete Pulse function (with a statically-known spec) as a
   function pointer. pre/post are explicit to avoid higher-order-unification
   failures. *)
val of_fn (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: (x:a -> stt b (pre x) (fun r -> post x r))) : func_ptr a b

(* `of_fn` produces a pointer valid at its own spec. This ghost step introduces
   the `is_valid` resource directly, so callers can obtain `is_valid (of_fn ..) ..`
   without folding a pure `valid` fact by hand. *)
val of_fn_valid (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: (x:a -> stt b (pre x) (fun r -> post x r)))
  : stt_ghost unit emp_inames emp (fun _ -> is_valid (of_fn pre post f) pre post)

(* Weaken the spec of a valid pointer: given ghost coercions turning the new
   precondition into the old one and the old postcondition into the new one,
   validity transfers from `(pre, post)` to `(pre', post')`.

   (This is the `weaken` of func-pointer-spec.md, with its `stt_ghost` argument
   types made well-formed: each coercion is a ghost computation consuming the
   source slprop and producing the target slprop.) `valid` is abstract, so this
   axiom is what lets a validity fact move across a spec change. *)
val weaken (#a #b: Type0) (f: func_ptr a b)
  (pre: a -> slprop) (post: a -> b -> slprop)
  (pre': a -> slprop) (post': a -> b -> slprop)
  (wpre:  (x:a -> stt_ghost unit emp_inames (pre' x) (fun _ -> pre x)))
  (wpost: (x:a -> y:b -> stt_ghost unit emp_inames (post x y) (fun _ -> post' x y)))
  : stt_ghost unit emp_inames
      (is_valid f pre post)
      (fun _ -> (is_valid f pre' post'))

(* Call through a valid function pointer. The validity witness is a squashed
   proof argument. This is the single, uniform primitive for every indirect
   call: the caller evaluates the callee to a `func_ptr` value and supplies the
   `is_valid f pre post` fact (for a concrete `of_fn`, via the `of_fn_valid`
   ghost step; for a callback parameter, from its precondition). `pre`/`post` are
   explicit because SMT will not solve for the higher-order spec metavariables.

   The postcondition also RETURNS `is_valid f pre post`: validity is a pure,
   persistent fact (`is_valid f pre post = pure (valid f pre post)`), and calling
   through a pointer does not invalidate it. Returning it lets a caller that
   carries `is_valid` in both its pre- and postcondition (e.g. a callback
   parameter annotated with a `_refine((_slprop) is_valid $(this) ..)`) thread the
   fact across the call. Callers that do not need it afterwards simply drop the
   surplus pure fact. *)
val call (#a #b: Type0) (pre: a -> slprop) (post: a -> b -> slprop)
  (f: func_ptr a b)  (x: a)
  : stt b (is_valid f pre post  ** pre x) (fun r -> is_valid f pre post ** post x r)

(* Decidable null test, so C `if (fp)` / `fp == NULL` can be translated. *)
val is_null (#a #b: Type0) (f: func_ptr a b) : (r: bool { r <==> f == null a b })

instance inhabited_func_ptr (a b: Type0) : inhabited (func_ptr a b) = { witness = null a b }
instance has_zero_default_func_ptr (a b: Type0) : has_zero_default (func_ptr a b) = { zero_default = null a b }

(* `has_is_null` instance so a function-pointer parameter can be marked `_nullable`
   (the `_refine` refinement is then wrapped in `unless_null`). Analogous to the
   `ref`/`array` instances in `Pulse.Lib.C.Nullable`; `test_null` is just `is_null`. *)
instance has_is_null_func_ptr (a b: Type0) : Pulse.Lib.C.Nullable.has_is_null (func_ptr a b) =
  { test_null = (fun f -> is_null f) }
