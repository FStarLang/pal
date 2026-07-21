#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* ==========================================================================
 * Function-pointer tests against the axiomatized Pulse.Lib.C.FuncPtr library.
 *
 * Layout:
 *   - The ACTIVE section holds every example that currently verifies
 *     (`make -C func_pointer verify-one MODULE=Func_<name>`).
 *   - The STAGED section (`#if 0`) holds the examples that do NOT yet verify,
 *     grouped into stages that mirror STATUS.md:
 *       Stage 1  Callback parameters (abstract func_ptr param)
 *       Stage 2  Concrete store + call (of_fn_valid ghost-step candidates)
 *       Stage 3  Join family
 *       Stage 4  Function pointers as data / control flow
 *       Stage 5  Advanced / edge cases
 *
 * Verifiability is conveyed only by the `[verifies]` / `[not yet verified]`
 * comment tags, never by the function names. See STATUS.md for the full table.
 * ========================================================================== */

/* ---- shared helper callees (each verifies on its own) ---- */

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t subtract(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100 && a > b)
    _ensures(return == a - b)
{
    return a - b;
}

int32_t neg(int32_t a)
    _requires(a > -100 && a < 100)
    _ensures(return == -a)
{
    return -a;
}

uint32_t combine(uint8_t a, uint32_t b, int32_t c)
    _requires(b < 100 && c > 0 && c < 100)
    _ensures(return == (uint32_t) a + b)
{
    return (uint32_t) a + b;
}

void do_nothing(void)
{
}

/* ---- shared type aliases (pure declarations, referenced by staged code) ---- */

typedef int32_t (*binop)(int32_t, int32_t);

/* A function TYPE (not a pointer); used by func_type_decay (Stage 2). */
typedef int32_t binop_fn(int32_t, int32_t);

/* ==========================================================================
 * ACTIVE: currently verifying examples
 * ========================================================================== */

/* [verifies] A function-pointer local stored but never called. At scope exit the
   `let mut` local is released by relinquishing back to a plain `pts_to`. */
void store_no_call(void)
{
    int32_t (*fp)(int32_t, int32_t) = add;
}

/* [verifies] Null initializer `= 0` and a null check `fp == 0`. The
   integer-literal `0` in a function-pointer context lowers to
   `Pulse.Lib.C.FuncPtr.null`, and `fp == 0` to `is_null`. */
int32_t use_null_init(void)
    _ensures(return == 0)
{
    int32_t (*fp)(int32_t, int32_t) = 0;
    if (fp == 0)
        return 0;
    return 1;
}

/* [verifies] Truthiness of a null pointer: `if (fp)` lowers to
   `not (is_null fp)`. */
int32_t use_null_truthiness(void)
    _ensures(return == 0)
{
    int32_t (*fp)(int32_t, int32_t) = 0;
    if (fp)
        return 1;
    return 0;
}

/* An indirect call `fp(x)` emits `call _ _ (!fp) args`, whose pre/post are
   inference holes. For a pointer that holds a concrete `of_fn ..` (a decayed
   named function) we close the holes by introducing the `is_valid` resource just
   before the call with a single `_ghost_stmt` invoking the `of_fn_valid` ghost
   step (which yields `is_valid (of_fn ..) ..` directly).

   `call`'s postcondition now RETURNS `is_valid f pre post` (validity is a
   persistent pure fact). A caller that does not itself export validity is left
   with that surplus resource, so it discards it *after* the call with
   `_ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _)` — placed right after the
   `return fp(..)`, where PAL's return-then-ghost rewrite runs it live before the
   return. The `_ _ _` holes match the unique leftover `is_valid` by its `mkey`
   pointer. (`apply` below is the exception: its `_refine` exports `is_valid` in
   the `ensures`, so it keeps — does not drop — the returned fact.) */

/* [verifies] Zero-arg / `void`-return callback (return value discarded). */
void use_void_cb(void)
{
    void (*cb)(void) = do_nothing;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_do_nothing.func_do_nothing_pre Func_do_nothing.func_do_nothing_post Func_do_nothing.func_do_nothing__fp);
    cb();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Function-to-pointer decay without `&`. */
int32_t use_no_amp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Explicit address-of `&`. */
int32_t use_amp(void)
    _ensures(return == 7)
{
    int32_t (*fp)(int32_t, int32_t) = &add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(3, 4);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Function pointer as a callback parameter. The `is_valid` fact is
   supplied via a `_refine((_slprop) is_valid $(this) ..)` refinement on the `op`
   parameter, so it lands in BOTH the generated `requires` and `ensures`. The
   in-body `op(a,b)` lowers to `call _ _ (!var_op) (a,b)`; `call` now RETURNS
   `is_valid var_op func_add_pre func_add_post` in its postcondition (validity is
   a persistent pure fact), so the fact threads across the call and discharges the
   ensures. Unlike the concrete-pointer callers above, `apply` therefore does NOT
   drop the returned `is_valid` — it keeps it to satisfy the `_refine` ensures. */
int32_t apply(int32_t (*op)(int32_t, int32_t)
                  _refine((_slprop) _inline_pulse(
                      Pulse.Lib.C.FuncPtr.is_valid $(this)
                          Func_add.func_add_pre Func_add.func_add_post)),
              int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

int32_t use_apply_add(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return apply(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Arity-1 callback parameter. Same `_refine` recipe as `apply`, with
   the arity-1 `neg` spec supplied on `op`. */
int32_t apply1(int32_t (*op)(int32_t)
                   _refine((_slprop) _inline_pulse(
                       Pulse.Lib.C.FuncPtr.is_valid $(this)
                           Func_neg.func_neg_pre Func_neg.func_neg_post)),
               int32_t x)
    _requires(x > -100 && x < 100)
    _ensures(return == -x)
{
    return op(x);
}

/* [verifies] Passing the concrete `neg` to the arity-1 callback. */
int32_t use_apply_neg(void)
    _ensures(return == -5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_neg.func_neg_pre Func_neg.func_neg_post Func_neg.func_neg__fp);
    return apply1(neg, 5);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Callback parameter whose type is spelled via the `binop` typedef;
   same `_refine` recipe as `apply`. */
int32_t apply_typedef(binop op
                          _refine((_slprop) _inline_pulse(
                              Pulse.Lib.C.FuncPtr.is_valid $(this)
                                  Func_add.func_add_pre Func_add.func_add_post)),
                      int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

/* [verifies] Typedef'd callback-parameter call site. */
int32_t typedef_callback(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return apply_typedef(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Weakened-callback spec: `apply_weaker` accepts a callback whose declared
   contract is WEAKER than what `subtract` provides. Its parameter carries the
   weak post `aw_post` (`return < a`, guarded by the same precondition as
   `subtract`), sharing `subtract`'s pre unchanged. A caller passing `subtract`
   (whose real post is `return == a - b`) must `weaken` subtract's validity to
   this weaker spec before the call — the `weaken_sub_to_aw` ghost helper below
   does exactly that, with an identity pre-coercion and a post-coercion that
   proves `return == a - b ==> return < a` under the shared precondition. */
_include_pulse(Apply_weaker_spec,
  unfold
  let aw_post (x_fp: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
              (return_1: Typedef_int32_t.ty_int32_t) : slprop =
    let var_a = fst x_fp in
    let var_b = snd x_fp in
    (Typedef_int32_t.ty_int32_t__pred var_a 1.0R) **
    (Typedef_int32_t.ty_int32_t__pred var_b 1.0R) **
    (Typedef_int32_t.ty_int32_t__pred return_1 1.0R) **
    pure (
      (((((0 < (id #int (Int32.v var_a))) && ((id #int (Int32.v var_a)) < 100)) &&
            (0 < (id #int (Int32.v var_b)))) && ((id #int (Int32.v var_b)) < 100)) &&
          (var_b `Int32.lt` var_a))
      ==> (return_1 `Int32.lt` var_a))

  ghost
  fn wpost_weak (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
                (y: Typedef_int32_t.ty_int32_t)
    requires Func_subtract.func_subtract_post x y
    ensures aw_post x y
  { () }

  ghost
  fn wpre_id (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
    requires Func_subtract.func_subtract_pre x
    ensures Func_subtract.func_subtract_pre x
  { () }

  ghost
  fn weaken_sub_to_aw
       (f: Pulse.Lib.C.FuncPtr.func_ptr
             (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t)
             Typedef_int32_t.ty_int32_t)
    requires Pulse.Lib.C.FuncPtr.is_valid f Func_subtract.func_subtract_pre Func_subtract.func_subtract_post
    ensures Pulse.Lib.C.FuncPtr.is_valid f Func_subtract.func_subtract_pre aw_post
  {
    Pulse.Lib.C.FuncPtr.weaken f
      Func_subtract.func_subtract_pre Func_subtract.func_subtract_post
      Func_subtract.func_subtract_pre aw_post
      wpre_id
      wpost_weak
  }
)

/* [verifies] A callback declared with a WEAKER postcondition than `subtract`
   provides. `op`'s validity uses `subtract`'s pre with the weakened `aw_post`. */
int32_t apply_weaker(int32_t (*op)(int32_t, int32_t)
                         _refine((_slprop) _inline_pulse(
                             Pulse.Lib.C.FuncPtr.is_valid $(this)
                                 Func_subtract.func_subtract_pre Apply_weaker_spec.aw_post)),
                     int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100 && a > b)
    _ensures(return < a)
{
    return op(a, b);
}

/* [verifies] Passing `subtract` (stronger post) to the weaker callback: seed
   `subtract`'s validity, `weaken` it to the callback's weaker spec, then call. */
int32_t weaken_callback(void)
    _ensures(return < 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
    _ghost_stmt(Apply_weaker_spec.weaken_sub_to_aw _);
    return apply_weaker(subtract, 5, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ==========================================================================
 * STAGED: examples that do not yet verify (kept under `#if 0`).
 * Grouped into stages mirroring STATUS.md; re-enabled incrementally as each
 * feature lands.
 * ========================================================================== */

/* --------------------------------------------------------------------------
 * Stage 1 - Callback parameters (abstract func_ptr param)  [ALL VERIFIED]
 *
 * The pointer is an abstract `func_ptr` PARAMETER (no `of_fn`), so the caller
 * must supply the `is_valid` fact. The working recipe (see active `apply`,
 * `apply1`, `apply_typedef` above): annotate the parameter with
 * `_refine((_slprop) is_valid $(this) <pre> <post>)`, landing `is_valid` in both
 * the `requires` and `ensures`; `call` returns `is_valid`, so it threads to the
 * ensures. Two variants need a little more machinery, still annotation-level:
 *   - `apply_weaker`/`weaken_callback`: the callback declares a WEAKER post; the
 *     caller `weaken`s subtract's validity first (see the `Apply_weaker_spec`
 *     `_include_pulse` module above).
 *   - `guarded_call`: a `_nullable` callback wraps validity in `unless_null`;
 *     the `if (fp)` branch `elim`s it to `is_valid` for the call and `intro`s it
 *     back for the ensures. (Requires the `has_is_null func_ptr` instance in the
 *     `Pulse.Lib.C.FuncPtr` library.)
 * -------------------------------------------------------------------------- */

int32_t guarded_call(int32_t (*fp)(int32_t, int32_t) _nullable
                         _refine((_slprop) _inline_pulse(
                             Pulse.Lib.C.FuncPtr.is_valid $(this)
                                 Func_add.func_add_pre Func_add.func_add_post)))
    _ensures(return == 0 || return == 5)
{
    if (fp) {
        _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_nonnull $(fp)
                        (Pulse.Lib.C.FuncPtr.is_valid $(fp) Func_add.func_add_pre Func_add.func_add_post));
        return fp(2, 3);
        _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_nonnull $(fp)
                        (Pulse.Lib.C.FuncPtr.is_valid $(fp) Func_add.func_add_pre Func_add.func_add_post));
    }
    return 0;
}


/* --------------------------------------------------------------------------
 * Stage 2 - Concrete store + call (of_fn_valid ghost-step candidates)
 *
 * Each stores a concrete named function into a local, then calls it. These are
 * strong candidates for the same `of_fn_valid` ghost-step recipe used by the
 * active `use_no_amp` / `use_amp`.
 * -------------------------------------------------------------------------- */

/* -- Stage C (read/copy-based) -- */

/* [verifies] Transitive copy from another pointer. */
int32_t use_transitive(void)
    _ensures(return == 5)
{
    int32_t (*fp1)(int32_t, int32_t) = add;
    int32_t (*fp2)(int32_t, int32_t) = fp1;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp2(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Reassignment (straight-line): the same pointer bound to
   different functions at different program points, each call statically
   resolving the current target. */
int32_t use_reassign(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    int32_t x = fp(1, 2);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    fp = subtract;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
    int32_t y = fp(8, 6);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return y + x;
}

/* [verifies] Reassignment through a copy of another pointer. */
int32_t use_reassign_copy(void)
    _ensures(return == 3)
{
    int32_t (*fp)(int32_t, int32_t) = subtract;
    int32_t (*src)(int32_t, int32_t) = add;
    fp = src;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(1, 2);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Arity-1 call. */
int32_t use_arity1(void)
    _ensures(return == -5)
{
    int32_t (*g)(int32_t) = neg;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_neg.func_neg_pre Func_neg.func_neg_post Func_neg.func_neg__fp);
    return g(5);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Higher-arity (arity 3), mixed-width tuple, no `&`. */
uint32_t use_arity3(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_combine.func_combine_pre Func_combine.func_combine_post Func_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Higher-arity (arity 3), mixed-width tuple, with `&`. */
uint32_t use_arity3_amp(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = &combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_combine.func_combine_pre Func_combine.func_combine_post Func_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Inline declarator type. */
int32_t use_inline_declarator(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] `typedef`'d function-pointer type. */
int32_t use_typedef(void)
    _ensures(return == 5)
{
    binop fp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Function-pointer type with const-qualified parameters: the
   qualifiers are ignored and the target is statically resolved. */
int32_t qualified_params(void)
    _ensures(return == 5)
{
    int32_t (*fp)(const int32_t, const int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] A function TYPE (not pointer) that decays to a pointer. */
int32_t func_type_decay(void)
    _ensures(return == 5)
{
    binop_fn *fp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Branch-local (conditional) dispatch: each branch binds its
   own single-assignment pointer to a different function, and calls it
   in-branch. */
int32_t use_conditional(int32_t sub)
    _requires(sub == 0 || sub == 1)
    _ensures(sub == 1 ==> return == 4)
    _ensures(sub == 0 ==> return == 12)
{
    if (sub == 1) {
        int32_t (*f)(int32_t, int32_t) = subtract;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
        return f(8, 4);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    } else {
        int32_t (*f)(int32_t, int32_t) = add;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
        return f(8, 4);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    }
}

/* [verifies] Casting a function pointer between compatible types (a cast
   on the stored value); the cast is peeled during static target resolution. */
int32_t use_cast(void)
    _ensures(return == 5)
{
    binop fp = (binop) add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Pointer-to-function-pointer. */
int32_t ptr_to_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    int32_t (**pp)(int32_t, int32_t) = &fp;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return (*pp)(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* --------------------------------------------------------------------------
 * Stage 3 - Join family
 *
 * The pointer is bound to different functions across a control-flow join and
 * called AFTER the merge, so no single static target exists at the call site.
 * Discharging these needs condition-aware validity reasoning at the join
 * (a branched/guard-split `is_valid`), which is not yet emitted.
 * -------------------------------------------------------------------------- */

_include_pulse(Reassign_join_spec,
  unfold
  let rj_pre (g: bool)
             (x_fp: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t)) : slprop =
    let var_a = (fst x_fp) in
    let var_b = (snd x_fp) in
    ((Typedef_int32_t.ty_int32_t__pred var_a 1.0R)) **
    ((Typedef_int32_t.ty_int32_t__pred var_b 1.0R)) **
    (pure (if g
           then ((((((0 < (id #int (Int32.v var_a))) && ((id #int (Int32.v var_a)) < 100)) &&
                     (0 < (id #int (Int32.v var_b))))
                   &&
                   ((id #int (Int32.v var_b)) < 100))
                 &&
                 (var_b `Int32.lt` var_a)))
           else (((((0 < (id #int (Int32.v var_a))) && ((id #int (Int32.v var_a)) < 100)) &&
                    (0 < (id #int (Int32.v var_b))))
                  &&
                  ((id #int (Int32.v var_b)) < 100)))))

  unfold
  let rj_post (g: bool)
              (x_fp: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
              (return_1: Typedef_int32_t.ty_int32_t) : slprop =
    let var_a = (fst x_fp) in
    let var_b = (snd x_fp) in
    ((Typedef_int32_t.ty_int32_t__pred var_a 1.0R)) **
    ((Typedef_int32_t.ty_int32_t__pred var_b 1.0R)) **
    ((Typedef_int32_t.ty_int32_t__pred return_1 1.0R)) **
    (pure (if g
           then ((((((((0 < (id #int (Int32.v var_a))) && ((id #int (Int32.v var_a)) < 100)) &&
                       (0 < (id #int (Int32.v var_b))))
                     &&
                     ((id #int (Int32.v var_b)) < 100))
                   &&
                   (var_b `Int32.lt` var_a)))) ==> (((return_1 = (var_a `Int32.sub` var_b)))))
           else (((((((0 < (id #int (Int32.v var_a))) && ((id #int (Int32.v var_a)) < 100)) &&
                     (0 < (id #int (Int32.v var_b))))
                   &&
                   ((id #int (Int32.v var_b)) < 100)))) ==> (((return_1 = (var_a `Int32.add` var_b)))))))

  ghost
  fn wpre_sub (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
    requires rj_pre true x
    ensures Func_subtract.func_subtract_pre x
  { rewrite (rj_pre true x) as (Func_subtract.func_subtract_pre x) }

  ghost
  fn wpost_sub (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
               (y: Typedef_int32_t.ty_int32_t)
    requires Func_subtract.func_subtract_post x y
    ensures rj_post true x y
  { rewrite (Func_subtract.func_subtract_post x y) as (rj_post true x y) }

  ghost
  fn wpre_add (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
    requires rj_pre false x
    ensures Func_add.func_add_pre x
  { rewrite (rj_pre false x) as (Func_add.func_add_pre x) }

  ghost
  fn wpost_add (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
               (y: Typedef_int32_t.ty_int32_t)
    requires Func_add.func_add_post x y
    ensures rj_post false x y
  { rewrite (Func_add.func_add_post x y) as (rj_post false x y) }

)

/* [verifies] `fp` is `subtract` or `add` chosen by a runtime guard, then called
   across the join. Each branch derives its per-branch validity with a single
   `FuncPtr.weaken` (after `of_fn_valid` for the named fn) landing directly on the
   common guard-pushed spec `(rj_pre g)(rj_post g)`; Pulse auto-introduces the join
   existential at the branch boundary and unfolds it after the merge (rj_pre/rj_post
   are `unfold`, so no manual fold/unfold or finish step is needed). */
int32_t reassign_join(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub)
    _ensures(_inline_pulse((exists* v. Pulse.Lib.Reference.pts_to $&(fp) v ** Pulse.Lib.C.FuncPtr.is_valid v (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub))) ** Pulse.Lib.Reference.pts_to $&(use_sub) (Ghost.reveal g_use_sub)))
    {
        fp = subtract;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp) Func_subtract.func_subtract_pre Func_subtract.func_subtract_post (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp) Func_add.func_add_pre Func_add.func_add_post (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Reassignment across a control-flow join, with the call AFTER the
   join. Structurally identical to `reassign_join`; verified via the same
   `_ensures`-on-`if` join contract, which carries the raw existential inline
   (`exists* v. pts_to fp v ** is_valid v (rj_pre g) (rj_post g)`) to hide the
   branch-differing pointer value behind an existential keyed on the common guard,
   so Pulse checks each arm against our contract instead of rebuilding the
   value-keyed merge. */
int32_t reassign_join_call(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub)
    _ensures(_inline_pulse((exists* v. Pulse.Lib.Reference.pts_to $&(fp) v ** Pulse.Lib.C.FuncPtr.is_valid v (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub))) ** Pulse.Lib.Reference.pts_to $&(use_sub) (Ghost.reveal g_use_sub)))
    {
        fp = subtract;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp) Func_subtract.func_subtract_pre Func_subtract.func_subtract_post (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp) Func_add.func_add_pre Func_add.func_add_post (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Assignment from an aggregate that yields a function pointer: read
   an element out of an array into a local, then call the local. Same recipe as
   `use_array_slot`: the emitter let-binds the stored value so `array_spec_initd`
   stays provable at the read, and `valid_cast` the read-back value before
   calling. */
int32_t assign_from_agg(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*fp)(int32_t, int32_t) = tbl[0];
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(fp));
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* --------------------------------------------------------------------------
 * Stage 4 - Function pointers as data / control flow
 *
 * The pointer lives in a struct field, array slot, union field, or heap cell.
 * When the stored value is a concrete decayed `of_fn`, the container read still
 * exposes it, so the call is recovered with the usual `of_fn_valid`/`drop_is_valid`
 * recipe (struct/union/heap ACTIVE below). The stack-local fixed-array cases and
 * the pointer-ownership callback remain staged under `#if 0` (emitter gaps; see
 * their comments and STATUS.md).
 * -------------------------------------------------------------------------- */

/* Plain aggregate holding a function pointer (no per-field contract). */
struct ops {
    int32_t (*op)(int32_t, int32_t);
};

/* [verifies] Function pointer stored in a struct field, then called. */
int32_t use_struct_field(void)
    _ensures(return == 5)
{
    struct ops o;
    _ghost_stmt($unfold-uninit(struct ops) $&(o));
    o.op = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Function pointer stored via a heap pointer, then called
   through the dereferenced slot. */
int32_t malloc_fp(void)
    _ensures(return == 5)
{
    int32_t (**pp)(int32_t, int32_t) =
        (int32_t (**)(int32_t, int32_t)) malloc(sizeof(int32_t (*)(int32_t, int32_t)));
    *pp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    int32_t r = (*pp)(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    free(pp);
    return r;
}

union op_or_int {
    int32_t (*op)(int32_t, int32_t);
    int32_t tag;
};

/* [verifies] Function pointer stored in a union field, then called. */
int32_t union_field(void)
    _ensures(return == 5)
{
    union op_or_int u;
    u.op = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return u.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Pointer/ownership callee, for ptr_arg_cb. */
void inc(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

/* Pointer / ownership argument threaded through an indirect call. The callee's
   relational spec (`*p == _old(*p) + 1`) is carried through the synthesized
   fnptr triple by threading the pointer's initial pointee value through the
   FuncPtr domain `a` (see `fnptr_domain_with_old` / `emit_fnptr_spec_core` in
   src/pass/emit.rs): the pre pins `pts_to p old_p`, the post existentially binds
   the current value `cur_p`, and `_old(*p)` resolves to the domain's `old_p`. */
void ptr_arg_cb(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    void (*f)(int32_t *) = inc;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_inc.func_inc_pre Func_inc.func_inc_post Func_inc.func_inc__fp);
    f(p);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] Function pointer stored in a fixed array element, then read back
   and called. The store emits `array_write` and the read emits `array_read`
   (stack-local fixed arrays are runtime `array` handles).

   Two ghost steps bridge the array's abstract spec to the concrete pointer:
   the emitter let-binds the stored `of_fn` value so `array_write` updates the
   spec against an opaque term (keeping `array_spec_initd` provable at the read),
   and `valid_cast` re-keys the `is_valid (of_fn ..)` fact from `of_fn_valid` to
   the value read back from the slot (which is only *provably* equal to it). */
int32_t use_array_slot(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*f)(int32_t, int32_t) = tbl[0];
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(f));
    return f(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* [verifies] A function pointer threaded through several layers (array element ->
   struct field) before the eventual call. Combines the `use_array_slot` recipe
   (`valid_cast` the array-read value) with the `use_struct_field` recipe
   (unfold the uninitialised struct before writing its field). */
int32_t multilayer(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*slot)(int32_t, int32_t) = tbl[0];
    struct ops o;
    _ghost_stmt($unfold-uninit(struct ops) $&(o));
    o.op = slot;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(slot));
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* --------------------------------------------------------------------------
 * Stage 5 - Advanced / edge cases (ACTIVE candidates)
 * -------------------------------------------------------------------------- */

/* Contract-carrying field, for the cross-function / vtable cases. */
struct ops_c {
    int32_t (*op)(int32_t, int32_t);
};

/* [verifies] Designated-initializer construction of a dispatch table. */
int32_t designated_vtable(void)
    _ensures(return == 5)
{
    struct ops_c o = { .op = add };
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Returns a function pointer chosen at runtime, with its validity threaded out
   through a guard-keyed `_ensures` (`is_valid return_1 (rj_pre g)(rj_post g)`,
   reusing `Reassign_join_spec`). Written as an explicit `if`/`else` (semantically
   identical to `return use_sub ? subtract : add;`) so that each arm has a C-source
   site to seed `of_fn_valid` + `weaken` the returned pointer's validity onto the
   guard-keyed spec. The verbatim ternary-return form has no per-arm site to seed
   those ghosts; see STATUS.md. */
binop select_op(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(_inline_pulse(Pulse.Lib.C.FuncPtr.is_valid return_1 (Reassign_join_spec.rj_pre (int32_to_bool var_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool var_use_sub))))
{
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub) {
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp) Func_subtract.func_subtract_pre Func_subtract.func_subtract_post (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
        return subtract;
    } else {
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp) Func_add.func_add_pre Func_add.func_add_post (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
        return add;
    }
}

/* [verifies] A function pointer used as a return value (via `select_op`). */
int32_t return_fp(void)
    _ensures(return == 5)
{
    binop fp = select_op(0);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Ownership predicate for a `struct ops_c *` whose `op` field is a valid `add`
   pointer. Carries `is_valid` on the field value so `dispatch` can call it. */
_include_pulse(Dispatch_spec,
  unfold let ops_c_valid ([@@@mkey] this: ref Struct_ops_c.struct_ops_c) (vo: Struct_ops_c.struct_ops_c) : slprop =
    Pulse.Lib.Reference.pts_to this vo **
    Pulse.Lib.C.FuncPtr.is_valid vo.Struct_ops_c.struct_ops_c__op Func_add.func_add_pre Func_add.func_add_post
)

_type(ops_c_val, Struct_ops_c.struct_ops_c)
_refine_value(ops_c_val vo, _inline_pulse(Dispatch_spec.ops_c_valid $(this) $(vo)))
_plain
typedef struct ops_c *ops_c_ptr;

/* [verifies] Cross-function dispatch: the pointer is written into a struct in one
   function and called through in `dispatch`, which cannot see the concrete
   target; the field's declared contract (`_refine_value`) carries `is_valid`. */
int32_t dispatch(ops_c_ptr o, int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return o->op(a, b);
}

/* [verifies] Caller for cross-function dispatch. */
int32_t use_dispatch(void)
    _ensures(return == 5)
{
    struct ops_c o;
    _ghost_stmt($unfold-uninit(struct ops_c) $&(o));
    o.op = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return dispatch(&o, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* --------------------------------------------------------------------------
 * Stage 5 - Advanced / edge cases
 *
 * Cross-function dispatch, return values, and indirect recursion.
 * -------------------------------------------------------------------------- */

/* [verifies] Array indexed by a runtime (non-constant) value, so no single
   static target exists at the call site. Both slots hold `add` and the index is
   constrained to `{0,1}`, so the read-back value is provably `add`; the same
   `valid_cast` recipe as `use_array_slot` re-keys its validity. */
int32_t array_runtime_idx(int32_t i)
    _requires(i == 0 || i == 1)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    tbl[1] = add;
    int32_t (*f)(int32_t, int32_t) = tbl[i];
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(f));
    return f(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

#if 0

/* [not yet verified — DEFERRED, emitter mutual-recursion gap] Indirect recursion
   through a function pointer. Taking the address of the function under definition
   (`self = rec_via_ptr`) decays to `of_fn .. func_rec_via_ptr__fp`, referencing the
   lifted triple `func_rec_via_ptr__fp`, whose body in turn calls `func_rec_via_ptr`.
   PAL emits `func_rec_via_ptr` and `func_rec_via_ptr__fp` as two SEPARATE top-level
   `fn`s (not a `fn rec .. and ..` group), with `func_rec_via_ptr` emitted first —
   so its `of_fn .. func_rec_via_ptr__fp` is a forward reference to a name defined
   later in the module (F* "Identifier not found: func_rec_via_ptr__fp", Error 72).
   Separately, any self-qualified annotation `Func_rec_via_ptr.func_rec_via_ptr_pre`
   creates a self-import of the interface (duplicate top-level names, Error 47). The
   fix is a `src/**` emitter change: emit the recursive function and its address-taken
   lifted `__fp` triple as a single mutually-recursive group. */
_rec int32_t rec_via_ptr(int32_t n)
    _requires(n >= 0 && n < 100)
    _ensures(return == 0)
    _decreases(n)
{
    int32_t (*self)(int32_t) = rec_via_ptr;
    if (n == 0)
        return 0;
    return self(n - 1);
}

#endif
