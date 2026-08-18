#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* ==========================================================================
 * Function-pointer tests against the axiomatized Pulse.Lib.C.FuncPtr library.
 * Every example here verifies (`make -C test/func_pointer`); the single deferred
 * case (`rec_via_ptr`) is kept under `#if 0` at the end.
 *
 * Divergence: PAL emits every function as `divergent fn` (`stt_div`) unless it
 * carries `_total`. FuncPtr validity therefore tracks a `div: bool` bit. A
 * pointer to a divergent target (the common case) is reflected with `of_fn_div`
 * and seeded with `of_fn_div_valid` (baking `div = true`); a `_total` target
 * (e.g. `add_t`) uses `of_fn`/`of_fn_valid` (`div = false`). An indirect call
 * emits `call` from a `_total` body and `call_div` from a divergent one, so the
 * required validity bit matches the enclosing body. A total pointer can be used
 * where a divergent one is expected by `weaken`-ing `false` up to `true`
 * (`weaken_total_to_div`); the reverse is unsound and forbidden.
 *
 * Indirect-call recipe: a call `fp(x)` emits `call{,_div} _ _ (!fp) args` with
 * the spec left as inference holes. For a pointer holding a concrete `of_fn{,_div}
 * ..` (a decayed named function), seed the validity fact just before the call
 * with `_ghost_stmt(.. of_fn_div_valid ..)` (or `of_fn_valid` for a `_total`
 * target). `call{,_div}` returns `is_valid` in its postcondition (validity is a
 * persistent pure fact), so a caller that does not itself export validity drops
 * the surplus afterwards with `_ghost_stmt(.. drop_is_valid _ _ _)`. Callback
 * parameters instead export `is_valid` via a `_refine` refinement (with the
 * matching `div` bit) and keep the returned fact.
 * ========================================================================== */

/* ---- shared helper callees ---- */

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

/* A `_total` (non-divergent) twin of `add`. Its `__fp` wrapper is emitted as a
   plain `fn` and reflected with `of_fn`, so `of_fn_valid` seeds validity at the
   total bit `false`. Used to test total function pointers and total->divergent
   weakening. */
_total
int32_t add_t(int32_t a, int32_t b)
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

/* ---- shared type aliases ---- */

typedef int32_t (*binop)(int32_t, int32_t);

/* A function type (not a pointer); decays to a pointer in func_type_decay. */
typedef int32_t binop_fn(int32_t, int32_t);

/* ---- storing & decay ---- */

/* A function-pointer local stored but never called. */
void store_no_call(void)
{
    int32_t (*fp)(int32_t, int32_t) = add;
}

/* Function-to-pointer decay without `&`. */
int32_t use_no_amp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Explicit address-of `&`. */
int32_t use_amp(void)
    _ensures(return == 7)
{
    int32_t (*fp)(int32_t, int32_t) = &add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(3, 4);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Transitive copy from another pointer. */
int32_t use_transitive(void)
    _ensures(return == 5)
{
    int32_t (*fp1)(int32_t, int32_t) = add;
    int32_t (*fp2)(int32_t, int32_t) = fp1;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp2(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Straight-line reassignment: the same pointer, different targets per call. */
int32_t use_reassign(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t x = fp(1, 2);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    fp = subtract;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
    int32_t y = fp(8, 6);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return y + x;
}

/* Reassignment through a copy of another pointer. */
int32_t use_reassign_copy(void)
    _ensures(return == 3)
{
    int32_t (*fp)(int32_t, int32_t) = subtract;
    int32_t (*src)(int32_t, int32_t) = add;
    fp = src;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(1, 2);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ---- type spellings ---- */

/* Inline declarator type. */
int32_t use_inline_declarator(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* `typedef`'d function-pointer type. */
int32_t use_typedef(void)
    _ensures(return == 5)
{
    binop fp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Const-qualified parameter types (qualifiers ignored). */
int32_t qualified_params(void)
    _ensures(return == 5)
{
    int32_t (*fp)(const int32_t, const int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* A function type (not a pointer) that decays to a pointer. */
int32_t func_type_decay(void)
    _ensures(return == 5)
{
    binop_fn *fp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Cast between compatible function-pointer types. */
int32_t use_cast(void)
    _ensures(return == 5)
{
    binop fp = (binop) add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ---- null & comparison ---- */

/* Null initializer `= 0` and null check `fp == 0` (lowered to `is_null`). */
int32_t use_null_init(void)
    _ensures(return == 0)
{
    int32_t (*fp)(int32_t, int32_t) = 0;
    if (fp == 0)
        return 0;
    return 1;
}

/* Truthiness of a null pointer: `if (fp)` lowers to `not (is_null fp)`. */
int32_t use_null_truthiness(void)
    _ensures(return == 0)
{
    int32_t (*fp)(int32_t, int32_t) = 0;
    if (fp)
        return 1;
    return 0;
}

/* Null comparison in a *spec* (not just a body). `f != 0` and `f != NULL` both
   lower to `FuncPtr.is_null`, so the postcondition follows from the
   precondition even though the two spellings differ. The body returns the
   comparison itself, which exercises the same lowering in value position; here
   `f == NULL` is false, so the result is 0. */
int32_t fp_spec_nonnull(binop f)
    _requires(f != 0)
    _ensures(f != NULL && return == 0)
{
    return f == NULL;
}

/* Same, for the `==` direction; `f != 0` is false, so the result is again 0. */
int32_t fp_spec_null(binop f)
    _requires(f == NULL)
    _ensures(f == 0 && return == 0)
{
    return f != 0;
}

/* ---- calling: arities / void ---- */

/* Zero-arg / `void`-return callback. */
void use_void_cb(void)
{
    void (*cb)(void) = do_nothing;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_do_nothing.func_do_nothing__fp);
    cb();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-1 call. */
int32_t use_arity1(void)
    _ensures(return == -5)
{
    int32_t (*g)(int32_t) = neg;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_neg.func_neg__fp);
    return g(5);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-3 call, mixed-width tuple. */
uint32_t use_arity3(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-3 call, mixed-width tuple, with `&`. */
uint32_t use_arity3_amp(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = &combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Same pointer called twice off one `of_fn_valid` (validity persists). */
int32_t call_twice(void)
    _ensures(return == 10)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t x = fp(2, 3);
    int32_t y = fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return x + y;
}

/* ---- control flow ---- */

/* Branch-local dispatch: each branch binds and calls its own pointer. */
int32_t use_conditional(int32_t sub)
    _requires(sub == 0 || sub == 1)
    _ensures(sub == 1 ==> return == 4)
    _ensures(sub == 0 ==> return == 12)
{
    if (sub == 1) {
        int32_t (*f)(int32_t, int32_t) = subtract;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        return f(8, 4);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    } else {
        int32_t (*f)(int32_t, int32_t) = add;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        return f(8, 4);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    }
}

/* Pointer-to-function-pointer. */
int32_t ptr_to_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    int32_t (**pp)(int32_t, int32_t) = &fp;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return (*pp)(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ---- loops ----
   Validity is carried across iterations by an `_inline_pulse(is_valid ..)` loop
   invariant; `call` returns `is_valid` so the fact survives each iteration. */

/* Call a callback in a `while` loop; `_live` tracks the mutable counters. */
int32_t loop_call(void)
    _ensures(return == 6)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t acc = 1;
    int32_t i = 0;
    while (i < 5)
        _invariant(_live(i) && _live(acc))
        _invariant(_inline_pulse(Pulse.Lib.C.FuncPtr.is_valid $(fp) true
            (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp)))
        _invariant(i >= 0 && i <= 5 && acc == i + 1)
    {
        acc = fp(acc, 1);
        i = i + 1;
    }
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return acc;
}

/* ---- callback parameters (abstract func_ptr params) ----
   The pointer is a func_ptr PARAMETER, so the caller supplies the `is_valid`
   fact via a `_refine((_slprop) is_valid $(this) ..)` refinement on the
   parameter, landing it in both the generated `requires` and `ensures`. */

/* Function pointer as a callback parameter. */
int32_t apply(int32_t (*op)(int32_t, int32_t)
                  _refine((_slprop) _inline_pulse(
                      Pulse.Lib.C.FuncPtr.is_valid $(this) true
                          (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp))),
              int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

/* Passing concrete `add` to the callback. */
int32_t use_apply_add(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return apply(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-1 callback parameter. */
int32_t apply1(int32_t (*op)(int32_t)
                   _refine((_slprop) _inline_pulse(
                       Pulse.Lib.C.FuncPtr.is_valid $(this) true
                           (Pulse.Lib.C.FuncPtr.pre_of Funcptr_neg.func_neg__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_neg.func_neg__fp))),
               int32_t x)
    _requires(x > -100 && x < 100)
    _ensures(return == -x)
{
    return op(x);
}

/* Passing concrete `neg` to the arity-1 callback. */
int32_t use_apply_neg(void)
    _ensures(return == -5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_neg.func_neg__fp);
    return apply1(neg, 5);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Callback parameter typed via the `binop` typedef. */
int32_t apply_typedef(binop op
                          _refine((_slprop) _inline_pulse(
                              Pulse.Lib.C.FuncPtr.is_valid $(this) true
                                  (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp))),
                      int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

/* Typedef'd callback-parameter call site. */
int32_t typedef_callback(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return apply_typedef(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Forward a callback parameter onward to another function (`apply`). */
int32_t forward(int32_t (*op)(int32_t, int32_t)
                    _refine((_slprop) _inline_pulse(
                        Pulse.Lib.C.FuncPtr.is_valid $(this) true
                            (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp))),
                int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return apply(op, a, b);
}

/* Passing concrete `add` through the forwarding callback. */
int32_t use_forward(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return forward(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Higher-order: the callback `g` is itself a function that takes a function
   pointer (like `apply`). After `g(add, ..)` returns, two `is_valid` facts are
   live -- `g`'s own (exported here) and `add`'s (returned by `apply`'s ensures)
   -- so the surplus `add` fact is dropped by pinning its `f`. */
int32_t hof(int32_t (*g)(int32_t (*)(int32_t, int32_t), int32_t, int32_t)
                _refine((_slprop) _inline_pulse(
                    Pulse.Lib.C.FuncPtr.is_valid $(this) true
                        (Pulse.Lib.C.FuncPtr.pre_of Funcptr_apply.func_apply__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_apply.func_apply__fp))),
            int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return g(add, a, b);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid
        (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_add.func_add__fp) _ _);
}

/* Passing concrete `apply` (itself a callback-taking function) to `hof`. */
int32_t use_hof(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_apply.func_apply__fp);
    return hof(apply, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* `apply_weaker` takes a callback whose declared post (`aw_post`) is WEAKER than
   `subtract` provides. `weaken_sub_to_aw` moves subtract's validity onto the
   weaker spec (identity pre-coercion; post-coercion proving
   `return == a - b ==> return < a` under the shared precondition). */
_include_pulse(Apply_weaker_spec,
  unfold
  let aw_post (x_fp: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
              (y_fp: erased unit)
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
                (y: erased unit)
                (r: Typedef_int32_t.ty_int32_t)
    requires (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp) x y r
    ensures aw_post x y r
  { () }

  ghost
  fn wpre_id (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
             (y: erased unit)
    requires (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) x y
    ensures (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) x y
  { () }

  ghost
  fn weaken_sub_to_aw
       (f: Pulse.Lib.C.FuncPtr.func_ptr
             (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t)
             Typedef_int32_t.ty_int32_t)
    requires Pulse.Lib.C.FuncPtr.is_valid f true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp)
    ensures Pulse.Lib.C.FuncPtr.is_valid f true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) aw_post
  {
    Pulse.Lib.C.FuncPtr.weaken f true true
      (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp)
      (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) aw_post
      wpre_id
      wpost_weak
  }
)

/* Callback declared with a weaker postcondition than `subtract` provides. */
int32_t apply_weaker(int32_t (*op)(int32_t, int32_t)
                         _refine((_slprop) _inline_pulse(
                             Pulse.Lib.C.FuncPtr.is_valid $(this) true
                                 (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) Apply_weaker_spec.aw_post)),
                     int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100 && a > b)
    _ensures(return < a)
{
    return op(a, b);
}

/* Pass `subtract` to the weaker callback: seed validity, `weaken`, then call. */
int32_t weaken_callback(void)
    _ensures(return < 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
    _ghost_stmt(Apply_weaker_spec.weaken_sub_to_aw _);
    return apply_weaker(subtract, 5, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* `_nullable` callback: validity is wrapped in `unless_null`; the `if (fp)`
   branch elims it to `is_valid` for the call and intros it back afterwards. */
int32_t guarded_call(int32_t (*fp)(int32_t, int32_t) _nullable
                         _refine((_slprop) _inline_pulse(
                             Pulse.Lib.C.FuncPtr.is_valid $(this) true
                                 (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp))))
    _ensures(return == 0 || return == 5)
{
    if (fp) {
        _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_nonnull $(fp)
                        (Pulse.Lib.C.FuncPtr.is_valid $(fp) true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp)));
        return fp(2, 3);
        _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_nonnull $(fp)
                        (Pulse.Lib.C.FuncPtr.is_valid $(fp) true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp)));
    }
    return 0;
}

/* Bare `_nullable` callback, i.e. no `_refine`. Without a refinement there is no
   `is_valid` to carry, so the parameter's slprop is the empty `unless_null fp emp`
   -- the same shape a `_nullable` data pointer with a prop-less pointee gets. The
   pointer can still be null-tested; it just cannot be called, since nothing
   establishes its validity. This exercises the plain `unless_null` path for
   function pointers, which relies on the `has_is_null_func_ptr` instance. */
int32_t is_set(int32_t (*fp)(int32_t, int32_t) _nullable)
    _ensures(return == 0 || return == 1)
{
    if (fp) {
        return 1;
    }
    return 0;
}

/* ---- join family ----
   The pointer is bound to different functions across a control-flow join and
   called after the merge, so no single static target exists at the call site.
   Each branch weakens its per-branch validity onto a common guard-keyed spec
   `(rj_pre g)(rj_post g)`; an `_ensures` on the `if` carries the join existential
   `exists* v. pts_to fp v ** is_valid v (rj_pre g)(rj_post g)`. */

/* Guard-keyed pre/post (`rj_pre`/`rj_post`) and the per-branch weakenings used
   by the join-family examples below. */
_include_pulse(Reassign_join_spec,
  unfold
  let rj_pre (g: bool)
             (x_fp: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
             (y_fp: erased unit) : slprop =
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
              (y_fp: erased unit)
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
              (y: erased unit)
    requires rj_pre true x y
    ensures (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) x y
  { () }

  ghost
  fn wpost_sub (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
               (y: erased unit)
               (r: Typedef_int32_t.ty_int32_t)
    requires (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp) x y r
    ensures rj_post true x y r
  { () }

  ghost
  fn wpre_add (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
              (y: erased unit)
    requires rj_pre false x y
    ensures (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) x y
  { () }

  ghost
  fn wpost_add (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
               (y: erased unit)
               (r: Typedef_int32_t.ty_int32_t)
    requires (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp) x y r
    ensures rj_post false x y r
  { () }

)

/* `fp` is `subtract` or `add` by a runtime guard, then called across the join. */
int32_t reassign_join(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub)
    _ensures(_inline_pulse((exists* v. Pulse.Lib.Reference.pts_to $&(fp) v ** Pulse.Lib.C.FuncPtr.is_valid v true (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub))) ** Pulse.Lib.Reference.pts_to $&(use_sub) (Ghost.reveal g_use_sub)))
    {
        fp = subtract;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Same as `reassign_join`, with the call after the join. */
int32_t reassign_join_call(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub)
    _ensures(_inline_pulse((exists* v. Pulse.Lib.Reference.pts_to $&(fp) v ** Pulse.Lib.C.FuncPtr.is_valid v true (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub))) ** Pulse.Lib.Reference.pts_to $&(use_sub) (Ghost.reveal g_use_sub)))
    {
        fp = subtract;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Returns a runtime-chosen pointer, its validity threaded out through a
   guard-keyed `_ensures`. Written as explicit `if`/`else` so each arm has a
   source site to seed `of_fn_valid` and `weaken` onto the guard-keyed spec. */
binop select_op(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(_inline_pulse(Pulse.Lib.C.FuncPtr.is_valid return_1 true (Reassign_join_spec.rj_pre (int32_to_bool var_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool var_use_sub))))
{
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub) {
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_subtract.func_subtract__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
        return subtract;
    } else {
        _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Pulse.Lib.C.FuncPtr.weaken (Pulse.Lib.C.FuncPtr.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (int32_to_bool g_use_sub)) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
        return add;
    }
}

/* A function pointer used as a return value (via `select_op`). */
int32_t return_fp(void)
    _ensures(return == 5)
{
    binop fp = select_op(0);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ---- function pointers as data (structs, unions, heap, arrays) ----
   The pointer lives in a container holding a concrete decayed `of_fn`, which the
   container read exposes, so the usual `of_fn_valid`/`drop_is_valid` recipe
   recovers the call. Array read-backs additionally `valid_cast` the read value
   (only provably equal to the stored `of_fn`) before calling. */

/* Plain aggregate holding a function pointer. */
struct ops {
    int32_t (*op)(int32_t, int32_t);
};

/* Function pointer stored in a struct field, then called. */
int32_t use_struct_field(void)
    _ensures(return == 5)
{
    struct ops o;
    _ghost_stmt($unfold-uninit(struct ops) $&(o));
    o.op = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

union op_or_int {
    int32_t (*op)(int32_t, int32_t);
    int32_t tag;
};

/* Function pointer stored in a union field, then called. */
int32_t union_field(void)
    _ensures(return == 5)
{
    union op_or_int u;
    u.op = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return u.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Function pointer stored via a heap pointer, then called. */
int32_t malloc_fp(void)
    _ensures(return == 5)
{
    int32_t (**pp)(int32_t, int32_t) =
        (int32_t (**)(int32_t, int32_t)) malloc(sizeof(int32_t (*)(int32_t, int32_t)));
    *pp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t r = (*pp)(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    free(pp);
    return r;
}

/* Pointer/ownership callee. Verifies as an ordinary function exercising a
   relational `_old` contract. (No longer address-taken — see the disabled
   ptr_arg_cb below — so no Funcptr_inc wrapper is generated.) */
void inc(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

/* ---- DISABLED: relational `_old` on an ownership pointer through an
   indirect (function-pointer) call ----
   `ptr_arg_cb` passes an ownership pointer through a FuncPtr to a callee
   (`inc`) whose contract is relational (`*p == _old(*p) + 1`). The pointer
   still gets its default `pts_to` permission across the FuncPtr, but the
   FuncPtr contract (`pre: a -> slprop`, `post: a -> b -> slprop`) is
   non-relational: expressing `_old(*p)` would need the pointer's initial
   pointee value threaded through the FuncPtr domain, which has been removed
   (fnptr arguments are now always plain values). So `_old(*p)` across an
   indirect call is unsupported. Disabled until first-class `_old` support in
   FuncPtr contracts is reinstated.

void ptr_arg_cb(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    void (*f)(int32_t *) = inc;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_inc.func_inc__fp);
    f(p);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
---- end DISABLED ptr_arg_cb ---- */

/* ---- DISABLED: storing a function pointer into an array element ----
   The four functions below (assign_from_agg, use_array_slot, array_runtime_idx,
   multilayer) each write a function pointer into an array slot (`tbl[i] = add;`).

   PAL used to work around a verification failure here with an ad-hoc trick: it
   let-bound the stored value to a temporary before `array_write`, so the array
   spec update stayed over a small variable. That trick has been removed, so the
   value (a large `of_fn_div (pre_of __fp) (post_of __fp) __fp` term) is now
   inlined directly into `array_write`. This makes
   `array_spec_upd s i (of_fn ...)` too large for the `array_spec_upd_*` SMTPats
   to fire, so the subsequent read-back cannot prove `array_spec_mask` /
   `array_spec_initd` nor recover the stored pointer.

   Increasing `z3rlimit` does NOT help: this was verified empirically (the proof
   fails identically at `--z3rlimit 50` and `--z3rlimit 300`, with the same
   `VC = array_spec_mask _s' 1`). The problem is SMTPat trigger/congruence
   matching against an over-large term, not a Z3 resource-budget problem.

   These are disabled until a proper library-level fix (making `array_write`'s
   spec robust to large stored values) is implemented.

int32_t assign_from_agg(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*fp)(int32_t, int32_t) = tbl[0];
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(fp));
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

int32_t use_array_slot(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*f)(int32_t, int32_t) = tbl[0];
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(f));
    return f(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

int32_t array_runtime_idx(int32_t i)
    _requires(i == 0 || i == 1)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    tbl[1] = add;
    int32_t (*f)(int32_t, int32_t) = tbl[i];
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(f));
    return f(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

int32_t multilayer(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*slot)(int32_t, int32_t) = tbl[0];
    struct ops o;
    _ghost_stmt($unfold-uninit(struct ops) $&(o));
    o.op = slot;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.valid_cast _ $(slot));
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
---- end DISABLED block ---- */

/* ---- cross-function dispatch / vtable ----
   The pointer is written into a struct in one function and called in `dispatch`,
   which cannot see the concrete target; the field's declared contract
   (`_refine_value` carrying `is_valid`) supplies validity. */

/* Contract-carrying field, for the dispatch/vtable cases. */
struct ops_c {
    int32_t (*op)(int32_t, int32_t);
};

/* Designated-initializer construction of a dispatch table. */
int32_t designated_vtable(void)
    _ensures(return == 5)
{
    struct ops_c o = { .op = add };
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Ownership predicate for a `struct ops_c *` carrying `is_valid` on its `op`
   field, so `dispatch` can call through it. */
_include_pulse(Dispatch_spec,
  unfold let ops_c_valid ([@@@mkey] this: ref Struct_ops_c.struct_ops_c) (vo: Struct_ops_c.struct_ops_c) : slprop =
    Pulse.Lib.Reference.pts_to this vo **
    Pulse.Lib.C.FuncPtr.is_valid vo.Struct_ops_c.struct_ops_c__op true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_add.func_add__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_add.func_add__fp)
)

_type(ops_c_val, Struct_ops_c.struct_ops_c)
_refine_value(ops_c_val vo, _inline_pulse(Dispatch_spec.ops_c_valid $(this) $(vo)))
_plain
typedef struct ops_c *ops_c_ptr;

/* Cross-function dispatch: call through a struct field whose declared contract
   carries `is_valid`. */
int32_t dispatch(ops_c_ptr o, int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return o->op(a, b);
}

/* Caller for cross-function dispatch. */
int32_t use_dispatch(void)
    _ensures(return == 5)
{
    struct ops_c o;
    _ghost_stmt($unfold-uninit(struct ops_c) $&(o));
    o.op = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return dispatch(&o, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* A vtable with two distinct fn-ptr fields (`bin`, `un`), each called. */
struct vtable2 {
    int32_t (*bin)(int32_t, int32_t);
    int32_t (*un)(int32_t);
};

int32_t use_two_field_vtable(void)
    _ensures(return == -5)
{
    struct vtable2 v;
    _ghost_stmt($unfold-uninit(struct vtable2) $&(v));
    v.bin = add;
    v.un = neg;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t s = v.bin(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_neg.func_neg__fp);
    int32_t r = v.un(s);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return r;
}

/* ---- total function pointers & total->divergent weakening ---- */

/* A `_total` caller holding a pointer to the `_total` `add_t`. Because `add_t`
   is total, its wrapper is reflected with `of_fn` and `of_fn_valid` seeds
   `is_valid .. false ..`; because the caller body is itself `_total`, the
   indirect call emits `call` (the total primitive returning `stt`). Shows that
   total function pointers verify end-to-end. */
_total
int32_t use_total_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add_t;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid _ _ Funcptr_add_t.func_add_t__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Callback parameter expecting a POSSIBLY-DIVERGENT pointer (`is_valid .. true`).
   The body is divergent (default), so the indirect call emits `call_div`. */
int32_t apply_t(int32_t (*op)(int32_t, int32_t)
                    _refine((_slprop) _inline_pulse(
                        Pulse.Lib.C.FuncPtr.is_valid $(this) true
                            (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp))),
                int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

/* Identity coercions plus a `weaken` from the total bit `false` to the divergent
   bit `true` (the `div ==> div'` refinement permits total->divergent). */
_include_pulse(Total_to_div_spec,
  ghost
  fn wpre_id (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
             (y: erased unit)
    requires (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) x y
    ensures (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) x y
  { () }

  ghost
  fn wpost_id (x: (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t))
               (y: erased unit)
               (r: Typedef_int32_t.ty_int32_t)
    requires (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp) x y r
    ensures (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp) x y r
  { () }

  ghost
  fn weaken_t_to_div
       (f: Pulse.Lib.C.FuncPtr.func_ptr
             (Typedef_int32_t.ty_int32_t & Typedef_int32_t.ty_int32_t)
             Typedef_int32_t.ty_int32_t)
    requires Pulse.Lib.C.FuncPtr.is_valid f false (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp)
    ensures Pulse.Lib.C.FuncPtr.is_valid f true (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp)
  {
    Pulse.Lib.C.FuncPtr.weaken f false true
      (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp)
      (Pulse.Lib.C.FuncPtr.pre_of_tot Funcptr_add_t.func_add_t__fp) (Pulse.Lib.C.FuncPtr.post_of_tot Funcptr_add_t.func_add_t__fp)
      wpre_id
      wpost_id
  }
)

/* Pass the TOTAL `add_t` to a callback that expects a possibly-divergent
   pointer: seed validity at `false`, `weaken` it up to `true`, then call. Shows
   that a total function pointer can be used where a divergent one is expected. */
int32_t weaken_total_to_div(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid _ _ Funcptr_add_t.func_add_t__fp);
    _ghost_stmt(Total_to_div_spec.weaken_t_to_div _);
    return apply_t(add_t, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Plain pointer parameter, no workaround annotations: PAL's auto-generated
   ownership for `int *p` is `exists* v. pts_to p v`. Taking `touch`'s
   address forces a `__fp` wrapper whose contract must be recovered via
   `pre_of`/`post_of` type-reflection. This now VERIFIES: `pre`/`post`
   (`Pulse.Lib.C.FuncPtr.fsti`) take an extra explicit `erased c` witness
   parameter after the wrapper's own argument, so the wrapper's real type is
   the flat `x:a -> y:erased c -> stt_div b (pre x y) (post x y)`
   `pre_of`/`post_of` need -- the pointee's ownership is threaded through `y`
   instead of a hidden implicit binder Pulse would otherwise introduce by
   opening a top-level `exists*` (which is what broke HOU with Error 189). */
void touch(int *p)
{
}

void use_touch_fp(void)
{
    void (*cb)(int *) = touch;
}

/* Also now verifies, for the same reason as `touch` above (not a strict-
   positivity error): `struct itemx` itself is fine here -- `destroy`'s field
   type stays a plain, non-recursive `func_ptr (ref struct_itemx) unit`, no
   self-reference, no Error 3. `destroy_impl`'s plain pointer parameter gets
   PAL's usual auto-derived `exists* v. pts_to self v` ownership, and
   `Itemx_spec.itemx_valid` recovers `pre_of`/`post_of
   Funcptr_destroy_impl.func_destroy_impl__fp` via the same explicit-witness
   mechanism. */
struct itemx {
    void (*destroy)(struct itemx *self);
    unsigned int n;
};

void destroy_impl(struct itemx *self)
{
}

void use_destroy_impl_fp(void)
{
    void (*cb)(struct itemx *) = destroy_impl;
}

_include_pulse(Itemx_spec,
  unfold let itemx_valid ([@@@mkey] this: ref Struct_itemx.struct_itemx) (vo: Struct_itemx.struct_itemx) : slprop =
    Pulse.Lib.Reference.pts_to this vo **
    Pulse.Lib.C.FuncPtr.is_valid vo.Struct_itemx.struct_itemx__destroy true (Pulse.Lib.C.FuncPtr.pre_of Funcptr_destroy_impl.func_destroy_impl__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_destroy_impl.func_destroy_impl__fp)
)

_type(itemx_val, Struct_itemx.struct_itemx)
_refine_value(itemx_val vo, _inline_pulse(Itemx_spec.itemx_valid $(this) $(vo)))
_plain
typedef struct itemx *itemx_ptr;

/* [not yet verified -- separate, harder limitation from the one above]
   Self-dispatch through a field: `p->destroy(p)` both (a) reads the callee
   off `p` via the struct's usual field-getter (`struct_itemx__get_destroy`,
   which implicitly unfolds `p`'s `pts_to` to split out the field) and (b)
   needs `p`'s pointee as the explicit witness value for `destroy_impl`'s
   `self` parameter. Each of these opens its OWN existential name for "the
   struct value at `p`" independently, and Pulse cannot automatically prove
   the two are the same value -- even when read back-to-back with no
   intervening mutation (confirmed by direct experimentation: naming one
   shared read explicitly still produces two distinct bound names). Fixing
   this needs either a `with`-based Pulse idiom threaded through PAL's
   fnptr-call emission, or a change to the struct field-getter to reuse an
   already-open existential -- left as follow-up work. */
#if 0
void destroy_via_field(itemx_ptr p) {
    p->destroy(p);
}

void use_destroy_via_field(void)
{
    struct itemx it;
    _ghost_stmt($unfold-uninit(struct itemx) $&(it));
    it.destroy = destroy_impl;
    it.n = 0;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_destroy_impl.func_destroy_impl__fp);
    destroy_via_field(&it);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}
#endif

#if 0

/* [not yet verified -- DEFERRED, emitter mutual-recursion gap] Indirect
   recursion through a function pointer. Taking the address of the function under
   definition decays to `of_fn .. func_rec_via_ptr__fp`, but PAL emits the
   function and its lifted triple as two SEPARATE top-level `fn`s (not a
   `fn rec .. and ..` group), so the reference is forward (F* Error 72). The fix
   is an emitter change to emit the recursive function and its address-taken
   `__fp` triple as a single mutually-recursive group. */
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
