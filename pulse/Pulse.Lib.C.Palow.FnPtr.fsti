module Pulse.Lib.C.Palow.FnPtr
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr

(* ============================================================================
   Function pointers in Palow.

   A function pointer here is a `ptr` -- the same `ptr` a data pointer is. That
   is the whole difference from `Pulse.Lib.C.FuncPtr`, which indexes the pointer
   type by the argument and return types, and it is the same decision that
   collapsed the type-indexed reference type: a code address is an address. The
   payoff is that storage comes for free. A function pointer in a local, a
   field, an array element or a global is stored, read and written by
   `ptr_repr`/`ptr_pts_to`/`ptr_read`/`ptr_write` with no new representation,
   no new machine axiom, and no per-C-function-type unrolling; and a cast
   between two function-pointer types is the identity, because there is only
   one type.

   What a function pointer's *value* means -- which Pulse specification the code
   at that address satisfies -- is not carried by its bytes. It is a separate,
   pure relation `valid f div pre post`, exactly as in `Pulse.Lib.C.FuncPtr`,
   and it is unchanged by the collapse: it never mentioned memory in the first
   place. `div` discriminates a pointer to a TOTAL Pulse function (callable via
   `call`) from one to a POSSIBLY-DIVERGENT function (callable via `call_div`);
   PAL emits every function as divergent unless it is `_total`.

   AXIOMS (the trusted core):
     - valid           : "the code at `f` meets this spec, at divergence `div`"
     - of_fn           : reflect a concrete TOTAL Pulse function as an address
     - of_fn_valid     : `of_fn` is valid at its own spec, `div = false`
     - of_fn_div       : reflect a concrete DIVERGENT Pulse function
     - of_fn_div_valid : `of_fn_div` is valid at its own spec, `div = true`
     - weaken          : move validity across a spec weakening and/or total->div
     - call            : indirect call of a TOTAL pointer (returns `stt`)
     - call_div        : indirect call of a DIVERGENT pointer (`stt_div`)

   DERIVED (nothing new assumed):
     - is_valid        : `pure (valid ..)`, hence persistent
     - drop_is_valid   : proven, `unfold`s to `emp`
     - valid_cast      : proven, moves validity across a value equality
     - prevent_lifting : an `unfold` identity used as a syntactic barrier

   The null function pointer is `Pulse.Lib.C.Palow.Ptr.null` and the null test
   is `is_null` from the same module -- another consequence of the collapse.

   Every combinator is parametrized by a witness type `c`, with `pre`/`post`
   taking a `c`-typed argument and the wrapped function taking a matching,
   EXPLICIT `erased c` parameter after `x:a`. This lets a pointer parameter's
   ownership (normally `exists* v. p_pts_to p 1.0R v` in `requires`) be
   expressed as `pre x v` for an explicit `v` instead of `exists* v. pre x v`.
   It matters because Pulse elaborates a top-level `exists*` in `requires` by
   opening it into a HIDDEN implicit binder after `x`, which defeats
   `pre_of`/`post_of`'s higher-order unification below (F* Error 189: the
   wrapper's type no longer has the flat `x:a -> stt_div b (pre x) (post x)`
   shape they need). An explicit witness parameter sidesteps this. A pointer
   with no such parameter instantiates `c = unit` and passes `hide ()`.
   ============================================================================ *)

(* `valid f div pre post`: the code at address `f` meets the spec `(pre, post)`;
   `div` records whether it may diverge. A pure prop, so `is_valid` is a
   persistent fact threadable without touching the heap -- and, unlike a
   points-to, it says nothing about who owns the bytes at `f`, which is right:
   code is not an object anyone owns.

   `pre`/`post` may `reveal` the witness internally; it stays un-revealed at the
   outer `pre x y`/`post x y` application, so higher-order unification sees a
   genuine Miller pattern (`?pre` applied to plain variables). *)
val valid (#a #b #c: Type0) (f: ptr) (div: bool)
  (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop) : prop

let is_valid (#a #b #c: Type0) ([@@@mkey] f: ptr) (div: bool)
  (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop) : slprop =
  pure (valid f div pre post)

(* Drop a surplus `is_valid` back to `emp` (it is persistent). Proven, not
   axiomatized: `is_valid` unfolds to `pure`. `f` is `[@@@mkey]`, so the resource
   in context is matched by the pointer and `div`/`pre`/`post` are inferred. *)
ghost fn drop_is_valid (#a #b #c: Type0) (#div: bool) (f: ptr)
  (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  requires is_valid f div pre post
  ensures emp
{
  unfold (is_valid f div pre post);
}

(* Move `is_valid` across a provable address equality `f == g`. Needed to call
   through a pointer read back from a slot, where the read value is only
   provably (not syntactically) equal to the stored `of_fn ..`. *)
ghost fn valid_cast (#a #b #c: Type0) (#div: bool)
  (#pre: a -> erased c -> slprop) (#post: a -> erased c -> b -> slprop)
  (f g: ptr)
  requires is_valid f div pre post ** pure (f == g)
  ensures is_valid g div pre post
{
  unfold (is_valid f div pre post);
  fold (is_valid g div pre post);
}

(* Recover a function's pre/post directly from its *type*. PAL emits each `__fp`
   wrapper with its contract inlined into `requires`/`ensures`, so the wrapper's
   type is `x:a -> y:erased c -> stt[_div] b (pre x y) (fun r -> post x y r)`;
   these projectors name that pre/post without a separate `let`. `pulse_eager_unfold`
   reduces `pre_of f` back to that lambda so slprop matching still connects. *)
[@@pulse_eager_unfold]
unfold let pre_of (#a #b #c: Type0) (#pre: a -> erased c -> slprop) (#post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt_div b (pre x y) (fun r -> post x y r))) : (a -> erased c -> slprop) = pre
[@@pulse_eager_unfold]
unfold let post_of (#a #b #c: Type0) (#pre: a -> erased c -> slprop) (#post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt_div b (pre x y) (fun r -> post x y r))) : (a -> erased c -> b -> slprop) = post
[@@pulse_eager_unfold]
unfold let pre_of_tot (#a #b #c: Type0) (#pre: a -> erased c -> slprop) (#post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt b (pre x y) (fun r -> post x y r))) : (a -> erased c -> slprop) = pre
[@@pulse_eager_unfold]
unfold let post_of_tot (#a #b #c: Type0) (#pre: a -> erased c -> slprop) (#post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt b (pre x y) (fun r -> post x y r))) : (a -> erased c -> b -> slprop) = post

(* Reflect a concrete TOTAL Pulse function as an address. pre/post are explicit
   to avoid higher-order-unification failures. *)
val of_fn (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt b (pre x y) (fun r -> post x y r))) : ptr

(* Ghost step yielding `is_valid (of_fn ..) false ..`. *)
val of_fn_valid (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt b (pre x y) (fun r -> post x y r)))
  : stt_ghost unit emp_inames emp (fun _ -> is_valid (of_fn pre post f) false pre post)

(* Reflect a concrete POSSIBLY-DIVERGENT Pulse function as an address. *)
val of_fn_div (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt_div b (pre x y) (fun r -> post x y r))) : ptr

(* Ghost step yielding `is_valid (of_fn_div ..) true ..`. *)
val of_fn_div_valid (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt_div b (pre x y) (fun r -> post x y r)))
  : stt_ghost unit emp_inames emp (fun _ -> is_valid (of_fn_div pre post f) true pre post)

(* A reflected function is not null: it is the address of code that exists. *)
val of_fn_not_null (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt b (pre x y) (fun r -> post x y r)))
  : squash (~ (of_fn pre post f == null))
val of_fn_div_not_null (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: (x:a -> y:erased c -> stt_div b (pre x y) (fun r -> post x y r)))
  : squash (~ (of_fn_div pre post f == null))

(* Transfer validity across a spec weakening and/or a divergence relaxation. The
   refinement `div ==> div'` permits total->divergent (a total pointer is
   trivially a valid divergent one) but forbids the unsound divergent->total. *)
val weaken (#a #b #c: Type0) (f: ptr)
  (div: bool) (div': bool { div ==> div' })
  (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (pre': a -> erased c -> slprop) (post': a -> erased c -> b -> slprop)
  (wpre:  (x:a -> y:erased c -> stt_ghost unit emp_inames (pre' x y) (fun _ -> pre x y)))
  (wpost: (x:a -> y:erased c -> r:b -> stt_ghost unit emp_inames (post x y r) (fun _ -> post' x y r)))
  : stt_ghost unit emp_inames
      (is_valid f div pre post)
      (fun _ -> (is_valid f div' pre' post'))

(* Indirect call of a TOTAL pointer: consume `is_valid f false pre post ** pre x
   w`. pre/post are explicit (SMT will not solve the higher-order
   metavariables); the caller supplies the witness `w` explicitly. The post also
   RETURNS the `is_valid` (validity is persistent), so a caller can thread it
   across the call. Returns `stt`, so it is usable from any context. *)
val call (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: ptr) (x: a) (w: erased c)
  : stt b (is_valid f false pre post ** pre x w) (fun r -> is_valid f false pre post ** post x w r)

(* Indirect call of a POSSIBLY-DIVERGENT pointer: as `call`, but keyed on
   `is_valid f true ..` and returning `stt_div`. *)
val call_div (#a #b #c: Type0) (pre: a -> erased c -> slprop) (post: a -> erased c -> b -> slprop)
  (f: ptr) (x: a) (w: erased c)
  : stt_div b (is_valid f true pre post ** pre x w) (fun r -> is_valid f true pre post ** post x w r)

(* A semantic no-op on `slprop`s that acts as a SYNTACTIC barrier against
   Pulse's precondition lifting.

   The lifting described in the witness-parameter note above is a surface-AST
   transform: when Pulse can see a `with_pure` (or `exists*`) at the top of a
   `requires`, it opens the binder it carries into a HIDDEN implicit binder
   after the function's explicit parameters. That gives the wrapper a type with
   one more binder than `pre_of`/`post_of`'s flat pattern, so their higher-order
   unification fails with F* Error 189. Behind an application the frontend no
   longer sees a liftable head, so no binder is opened; `unfold` then erases
   this wrapper during typechecking, leaving the original `slprop` in place.

   The `ensures` needs no such treatment: postconditions are not lifted this
   way, and `post_of` matches them as emitted. *)
unfold let prevent_lifting (p: slprop) = p
