#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* Function-pointer tests against the axiomatized Pulse.Lib.C.FuncPtr library.
 * `rec_via_ptr` remains disabled (`#if 0` at the end).
 *
 * Divergence: every function is `divergent fn` unless `_total`. A pointer to
 * a divergent target uses `of_fn_div`/`of_fn_div_valid`; a `_total` target
 * uses `of_fn`/`of_fn_valid`. Calls use `call_div`/`call` to match. A total
 * pointer can `weaken` up to divergent, never the reverse.
 *
 * Indirect-call recipe: seed validity with `_ghost_stmt(.. of_fn_div_valid ..)`
 * before calling `fp(x)`; drop the returned `is_valid` fact afterwards with
 * `_ghost_stmt(.. drop_is_valid _ _ _)` unless it needs to be kept. Callback
 * parameters instead get `is_valid` via a `_refine` on the parameter. */

/* ---- shared helper callees ---- */

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

/* A `_total` (non-divergent) twin of `add`, for testing total function
   pointers and total->divergent weakening. */
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

_ghost_arg(uint32_t before)
void ghost_only(void)
    _requires(before < 100)
{
}

_total
_ghost_arg(uint32_t before)
_ghost_arg(uint32_t after)
uint32_t ghost_next(uint32_t value)
    _requires(value == before && before < 100 && after == before + 1)
    _ensures(return == after)
{
    return value + 1;
}

/* ---- shared type aliases ---- */

typedef int32_t (*binop)(int32_t, int32_t);

/* A function type (not a pointer); decays to a pointer in func_type_decay. */
typedef int32_t binop_fn(int32_t, int32_t);

/* ---- storing & decay ---- */

/* A function-pointer local stored but never called. */
/* Seeding `is_valid` when a function decays to an address, and putting it
   down again afterwards, is scaffolding the old translator needs written at
   the source level. Palow's emitter does both itself at every decay site, so
   under PALOW these statements are not merely unnecessary but duplicates that
   would be left over at the end of the function. */
#ifdef PALOW
#define _fp_ghost(x)
#else
#define _fp_ghost(x) _ghost_stmt(x)
#endif

/* Likewise for opening a local struct's storage before its fields are
   written one at a time: the old model needs the source to say so, Palow
   scatters and gathers the object itself. */
#ifdef PALOW
#define _unfold_uninit(T, p)
#else
#define _unfold_uninit(T, p) _ghost_stmt($unfold-uninit(T) p)
#endif

/* Both memory models axiomatize function pointers the same way, under
   different names: `Pulse.Lib.C.FuncPtr` for PAL's model and
   `Pulse.Lib.C.Palow.FnPtr` for Palow's. A one-line `include` gives the
   annotations below a single spelling that works for either, so the test can
   say what it is about instead of saying it twice.

   The genuine differences are two. PAL's `func_ptr a b` remembers the domain
   and range; Palow's `ptr` is one type for every pointer and forgets them,
   since C does too. And the two emitters build a callback's ghost witness
   differently -- PAL pairs the resource witness with the `_ghost_arg` tuple,
   Palow has neither here -- so the witness type gets a name as well. The shim
   names both away. */
#ifdef PALOW
_include_pulse(Fp_shim,
  include Pulse.Lib.C.Palow.FnPtr

  let func_ptr (a b: Type0) = Pulse.Lib.C.Palow.Ptr.ptr
  let i32 = FStar.Int32.t
  let wit = unit
  unfold let i32_pred (x: i32) (p: perm) : slprop = emp
)
#else
_include_pulse(Fp_shim,
  include Pulse.Lib.C.FuncPtr

  let i32 = Typedef_int32_t.ty_int32_t
  let wit = unit & unit
  unfold let i32_pred (x: i32) (p: perm) : slprop =
    Typedef_int32_t.ty_int32_t__pred x p
)
#endif

void store_no_call(void)
{
    int32_t (*fp)(int32_t, int32_t) = add;
}

/* The erased call witness supplies before without changing the C signature. */
void take_pointer(void)
{
    void (*fp)(void) = ghost_only;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_ghost_only.func_ghost_only__fp);
#ifdef PALOW
    /* Palow's call witness is the tuple of ghost arguments alone: ownership
       is named in the contract, so there is no leading unit component. */
    _ghost_stmt(Pulse.Lib.C.FuncPtr.eta_expanded_erased (hide 0ul));
#else
    _ghost_stmt(Pulse.Lib.C.FuncPtr.eta_expanded_erased (hide ((), 0ul)));
#endif
    fp();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Multiple ghosts must be forwarded from the same witness into pre and post. */
_total
uint32_t take_pointer_ghost_args(void)
    _ensures(return == 42)
{
    uint32_t (*fp)(uint32_t) = ghost_next;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid _ _ Funcptr_ghost_next.func_ghost_next__fp);
#ifdef PALOW
    _ghost_stmt(Pulse.Lib.C.FuncPtr.eta_expanded_erased (hide (41ul, 42ul)));
#else
    _ghost_stmt(Pulse.Lib.C.FuncPtr.eta_expanded_erased (hide ((), (41ul, 42ul))));
#endif
    uint32_t result = fp(41);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    return result;
}

/* Function-to-pointer decay without `&`. */
int32_t use_no_amp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Explicit address-of `&`. */
int32_t use_amp(void)
    _ensures(return == 7)
{
    int32_t (*fp)(int32_t, int32_t) = &add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(3, 4);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Transitive copy from another pointer. */
int32_t use_transitive(void)
    _ensures(return == 5)
{
    int32_t (*fp1)(int32_t, int32_t) = add;
    int32_t (*fp2)(int32_t, int32_t) = fp1;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp2(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Straight-line reassignment: the same pointer, different targets per call. */
int32_t use_reassign(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t x = fp(1, 2);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    fp = subtract;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
    int32_t y = fp(8, 6);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    return y + x;
}

/* Reassignment through a copy of another pointer. */
int32_t use_reassign_copy(void)
    _ensures(return == 3)
{
    int32_t (*fp)(int32_t, int32_t) = subtract;
    int32_t (*src)(int32_t, int32_t) = add;
    fp = src;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(1, 2);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* ---- type spellings ---- */

/* Inline declarator type. */
int32_t use_inline_declarator(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* `typedef`'d function-pointer type. */
int32_t use_typedef(void)
    _ensures(return == 5)
{
    binop fp = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Const-qualified parameter types (qualifiers ignored). */
int32_t qualified_params(void)
    _ensures(return == 5)
{
    int32_t (*fp)(const int32_t, const int32_t) = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* A function type (not a pointer) that decays to a pointer. */
int32_t func_type_decay(void)
    _ensures(return == 5)
{
    binop_fn *fp = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Cast between compatible function-pointer types. */
int32_t use_cast(void)
    _ensures(return == 5)
{
    binop fp = (binop) add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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

/* Null comparison in a spec: `f != 0` and `f != NULL` both lower to
   `is_null`, so the ensures holds regardless of spelling. */
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

/* ---- null in argument position ----
   `null` takes two explicit type arguments, so the emitted term is an
   application and must be parenthesized to survive juxtaposition at a call
   site. `take_cb` deliberately does not call its callback, so no `is_valid`
   witness is needed and the proof stays trivial. */

int32_t take_cb(int32_t x, int32_t (*f)(int32_t))
    _ensures(return == x)
{
    return x;
}

/* NULL as an argument. */
int32_t pass_null_cb(int32_t x)
    _ensures(return == x)
{
    return take_cb(x, NULL);
}

/* Bare `0` as an argument. */
int32_t pass_zero_cb(int32_t x)
    _ensures(return == x)
{
    return take_cb(x, 0);
}

/* Explicit cast to the function-pointer type as an argument. */
int32_t pass_cast_cb(int32_t x)
    _ensures(return == x)
{
    return take_cb(x, (int32_t (*)(int32_t))0);
}

/* Via a local; this path already worked, keep it covered. */
int32_t pass_local_cb(int32_t x)
    _ensures(return == x)
{
    int32_t (*f)(int32_t) = NULL;
    return take_cb(x, f);
}

/* ---- calling: arities / void ---- */

/* Zero-arg / `void`-return callback. */
void use_void_cb(void)
{
    void (*cb)(void) = do_nothing;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_do_nothing.func_do_nothing__fp);
    cb();
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Arity-1 call. */
int32_t use_arity1(void)
    _ensures(return == -5)
{
    int32_t (*g)(int32_t) = neg;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_neg.func_neg__fp);
    return g(5);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Arity-3 call, mixed-width tuple. */
uint32_t use_arity3(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = combine;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Arity-3 call, mixed-width tuple, with `&`. */
uint32_t use_arity3_amp(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = &combine;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Same pointer called twice off one `of_fn_valid` (validity persists). */
int32_t call_twice(void)
    _ensures(return == 10)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t x = fp(2, 3);
    int32_t y = fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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
        _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        return f(8, 4);
        _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    } else {
        int32_t (*f)(int32_t, int32_t) = add;
        _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        return f(8, 4);
        _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    }
}

/* Pointer-to-function-pointer. */
int32_t ptr_to_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    int32_t (**pp)(int32_t, int32_t) = &fp;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return (*pp)(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* ---- loops ----
   Validity is carried across iterations by an `_inline_pulse(is_valid ..)` loop
   invariant; `call` returns `is_valid` so the fact survives each iteration. */

/* Call a callback in a `while` loop; `_live` tracks the mutable counters. */
int32_t loop_call(void)
    _ensures(return == 6)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t acc = 1;
    int32_t i = 0;
    while (i < 5)
        _invariant(_live(i) && _live(acc))
        _invariant(_inline_pulse(Fp_shim.is_valid $(fp) true
            (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp)))
        _invariant(i >= 0 && i <= 5 && acc == i + 1)
    {
        acc = fp(acc, 1);
        i = i + 1;
    }
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    return acc;
}

/* ---- callback parameters (abstract func_ptr params) ----
   A `_refine` on the parameter supplies the `is_valid` fact for the call. */

/* Function pointer as a callback parameter. */
int32_t apply(int32_t (*op)(int32_t, int32_t)
                  _refine((_slprop) _inline_pulse(
                      Fp_shim.is_valid $(this) true
                          (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp))),
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
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return apply(add, 2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Arity-1 callback parameter. */
int32_t apply1(int32_t (*op)(int32_t)
                   _refine((_slprop) _inline_pulse(
                       Fp_shim.is_valid $(this) true
                           (Fp_shim.pre_of Funcptr_neg.func_neg__fp) (Fp_shim.post_of Funcptr_neg.func_neg__fp))),
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
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_neg.func_neg__fp);
    return apply1(neg, 5);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Callback parameter typed via the `binop` typedef. */
int32_t apply_typedef(binop op
                          _refine((_slprop) _inline_pulse(
                              Fp_shim.is_valid $(this) true
                                  (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp))),
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
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return apply_typedef(add, 2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Forward a callback parameter onward to another function (`apply`). */
int32_t forward(int32_t (*op)(int32_t, int32_t)
                    _refine((_slprop) _inline_pulse(
                        Fp_shim.is_valid $(this) true
                            (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp))),
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
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return forward(add, 2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Higher-order: `g` itself takes a function pointer (like `apply`). Two
   `is_valid` facts are live after `g(add, ..)` -- `g`'s own and `add`'s --
   so the surplus `add` fact is dropped. */
int32_t hof(int32_t (*g)(int32_t (*)(int32_t, int32_t), int32_t, int32_t)
                _refine((_slprop) _inline_pulse(
                    Fp_shim.is_valid $(this) true
                        (Fp_shim.pre_of Funcptr_apply.func_apply__fp) (Fp_shim.post_of Funcptr_apply.func_apply__fp))),
            int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return g(add, a, b);
    _fp_ghost(Fp_shim.drop_is_valid
        (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) _ _);
}

/* Passing concrete `apply` (itself a callback-taking function) to `hof`. */
int32_t use_hof(void)
    _ensures(return == 5)
{
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_apply.func_apply__fp);
    return hof(apply, 2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* `apply_weaker` takes a callback whose declared post (`aw_post`) is weaker
   than `subtract` provides; `weaken_sub_to_aw` moves subtract's validity
   onto that weaker spec. */
_include_pulse(Apply_weaker_spec,
  unfold
  let aw_post (x_fp: (Fp_shim.i32 & Fp_shim.i32))
              (y_fp: erased Fp_shim.wit)
              (return_1: Fp_shim.i32) : slprop =
    let var_a = fst x_fp in
    let var_b = snd x_fp in
    (Fp_shim.i32_pred var_a 1.0R) **
    (Fp_shim.i32_pred var_b 1.0R) **
    (Fp_shim.i32_pred return_1 1.0R) **
    pure (
      (((((0 < (id #int (Int32.v var_a))) && ((id #int (Int32.v var_a)) < 100)) &&
            (0 < (id #int (Int32.v var_b)))) && ((id #int (Int32.v var_b)) < 100)) &&
          (var_b `Int32.lt` var_a))
      ==> (return_1 `Int32.lt` var_a))

  ghost
  fn wpost_weak (x: (Fp_shim.i32 & Fp_shim.i32))
                (y: erased Fp_shim.wit)
                (r: Fp_shim.i32)
    requires (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) x y r
    ensures aw_post x y r
  { () }

  ghost
  fn wpre_id (x: (Fp_shim.i32 & Fp_shim.i32))
             (y: erased Fp_shim.wit)
    requires (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) x y
    ensures (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) x y
  { () }

  ghost
  fn weaken_sub_to_aw
       (f: Fp_shim.func_ptr
             (Fp_shim.i32 & Fp_shim.i32)
             Fp_shim.i32)
    requires Fp_shim.is_valid f true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp)
    ensures Fp_shim.is_valid f true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) aw_post
  {
    Fp_shim.weaken f true true
      (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp)
      (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) aw_post
      (fun _ y -> y)
      wpre_id
      wpost_weak
  }
)

/* Callback declared with a weaker postcondition than `subtract` provides. */
int32_t apply_weaker(int32_t (*op)(int32_t, int32_t)
                         _refine((_slprop) _inline_pulse(
                             Fp_shim.is_valid $(this) true
                                 (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) Apply_weaker_spec.aw_post)),
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
    _ghost_stmt(Fp_shim.of_fn_div_valid (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) Funcptr_subtract.func_subtract__fp);
    _ghost_stmt(Apply_weaker_spec.weaken_sub_to_aw _);
    return apply_weaker(subtract, 5, 3);
    /* `apply_weaker` hands the weakened validity back, so it has to be
       dropped here.  Palow seeds a second, unweakened copy at the decay site
       and drops that one itself, which is why this drop has to name the specs
       it means instead of leaving them to inference. */
    _ghost_stmt(Fp_shim.drop_is_valid (Fp_shim.of_fn_div (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) Funcptr_subtract.func_subtract__fp) (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) Apply_weaker_spec.aw_post);
}

/* `_nullable` callback: validity is wrapped in `unless_null`; the `if (fp)`
   branch elims it to `is_valid` for the call and intros it back afterwards. */
int32_t guarded_call(int32_t (*fp)(int32_t, int32_t) _nullable
                         _refine((_slprop) _inline_pulse(
                             Fp_shim.is_valid $(this) true
                                 (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp))))
    _ensures(return == 0 || return == 5)
{
    if (fp) {
#ifdef PALOW
        /* Palow states a `_refine` on a `_nullable` parameter as it is
           written, without wrapping it in `unless_null`, so validity is
           already in hand inside the guard and there is nothing to eliminate
           or reintroduce. The precondition is correspondingly stronger --
           a caller must supply validity even to pass null -- which palow.md
           records as a known deviation. */
        return fp(2, 3);
#else
        _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_nonnull $(fp)
                        (Fp_shim.is_valid $(fp) true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp)));
        return fp(2, 3);
        _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_nonnull $(fp)
                        (Fp_shim.is_valid $(fp) true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp)));
#endif
    }
    return 0;
}

/* Bare `_nullable` callback, no `_refine`: no `is_valid` to carry, so the
   parameter's slprop is just `unless_null fp emp`. Can be null-tested but
   not called. Exercises `has_is_null_func_ptr`. */
int32_t is_set(int32_t (*fp)(int32_t, int32_t) _nullable)
    _ensures(return == 0 || return == 1)
{
    if (fp) {
        return 1;
    }
    return 0;
}

/* ---- join family ----
   The pointer is bound to different functions across a control-flow join,
   so no single static target exists at the call site. Each branch weakens
   its validity onto a common guard-keyed spec `(rj_pre g)(rj_post g)`,
   carried across the join by an `_ensures` on the `if`. */

/* Guard-keyed pre/post (`rj_pre`/`rj_post`) and the per-branch weakenings used
   by the join-family examples below. */
_include_pulse(Reassign_join_spec,
  unfold
  let rj_pre (g: bool)
             (x_fp: (Fp_shim.i32 & Fp_shim.i32))
             (y_fp: erased Fp_shim.wit) : slprop =
    let var_a = (fst x_fp) in
    let var_b = (snd x_fp) in
    ((Fp_shim.i32_pred var_a 1.0R)) **
    ((Fp_shim.i32_pred var_b 1.0R)) **
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
              (x_fp: (Fp_shim.i32 & Fp_shim.i32))
              (y_fp: erased Fp_shim.wit)
              (return_1: Fp_shim.i32) : slprop =
    let var_a = (fst x_fp) in
    let var_b = (snd x_fp) in
    ((Fp_shim.i32_pred var_a 1.0R)) **
    ((Fp_shim.i32_pred var_b 1.0R)) **
    ((Fp_shim.i32_pred return_1 1.0R)) **
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
  fn wpre_sub (x: (Fp_shim.i32 & Fp_shim.i32))
              (y: erased Fp_shim.wit)
    requires rj_pre true x y
    ensures (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) x y
  { () }

  ghost
  fn wpost_sub (x: (Fp_shim.i32 & Fp_shim.i32))
               (y: erased Fp_shim.wit)
               (r: Fp_shim.i32)
    requires (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) x y r
    ensures rj_post true x y r
  { () }

  ghost
  fn wpre_add (x: (Fp_shim.i32 & Fp_shim.i32))
              (y: erased Fp_shim.wit)
    requires rj_pre false x y
    ensures (Fp_shim.pre_of Funcptr_add.func_add__fp) x y
  { () }

  ghost
  fn wpost_add (x: (Fp_shim.i32 & Fp_shim.i32))
               (y: erased Fp_shim.wit)
               (r: Fp_shim.i32)
    requires (Fp_shim.post_of Funcptr_add.func_add__fp) x y r
    ensures rj_post false x y r
  { () }

)

/* `fp` is `subtract` or `add` by a runtime guard, then called across the join. */
#ifdef PALOW
/* A scalar parameter is a value in Palow, not a cell, so there is no ghost
   read to do: `use_sub` can be named directly in a contract. The local `fp`
   does have storage, and its ownership is Palow's `ptr_pts_to`. */
int32_t reassign_join(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    if (use_sub)
    _ensures(_inline_pulse(exists* v. ptr_pts_to $&(fp) 1.0R v ** Fp_shim.is_valid v true (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub)))))
    {
        fp = subtract;
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (fun _ y -> y) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (fun _ y -> y) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}
#else
int32_t reassign_join(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub)
    _ensures(_inline_pulse((exists* v. Pulse.Lib.Reference.pts_to $&(fp) v ** Fp_shim.is_valid v true (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub))) ** Pulse.Lib.Reference.pts_to $&(use_sub) (Ghost.reveal g_use_sub)))
    {
        fp = subtract;
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (fun _ y -> y) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (fun _ y -> y) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}
#endif

/* Same as `reassign_join`, with the call after the join. */
#ifdef PALOW
/* A scalar parameter is a value in Palow, not a cell, so there is no ghost
   read to do: `use_sub` can be named directly in a contract. The local `fp`
   does have storage, and its ownership is Palow's `ptr_pts_to`. */
int32_t reassign_join_call(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    if (use_sub)
    _ensures(_inline_pulse(exists* v. ptr_pts_to $&(fp) 1.0R v ** Fp_shim.is_valid v true (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub)))))
    {
        fp = subtract;
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (fun _ y -> y) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (fun _ y -> y) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}
#else
int32_t reassign_join_call(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(use_sub == 1 ==> return == 2)
    _ensures(use_sub == 0 ==> return == 4)
{
    int32_t (*fp)(int32_t, int32_t);
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub)
    _ensures(_inline_pulse((exists* v. Pulse.Lib.Reference.pts_to $&(fp) v ** Fp_shim.is_valid v true (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub))) ** Pulse.Lib.Reference.pts_to $&(use_sub) (Ghost.reveal g_use_sub)))
    {
        fp = subtract;
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (fun _ y -> y) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
    } else {
        fp = add;
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (fun _ y -> y) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
    }
    return fp(3, 1);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}
#endif

/* Returns a runtime-chosen pointer, its validity threaded out through a
   guard-keyed `_ensures`. Written as explicit `if`/`else` so each arm has a
   source site to seed `of_fn_valid` and `weaken` onto the guard-keyed spec. */
#ifdef PALOW
binop select_op(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(_inline_pulse(Fp_shim.is_valid $(return) true (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub)))))
{
    if (use_sub) {
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (fun _ y -> y) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
        return subtract;
    } else {
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool $(use_sub))) (fun _ y -> y) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
        return add;
    }
}
#else
binop select_op(int32_t use_sub)
    _requires(use_sub == 0 || use_sub == 1)
    _ensures(_inline_pulse(Fp_shim.is_valid return_1 true (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool var_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool var_use_sub))))
{
    _ghost_stmt(let g_use_sub = Pulse.Lib.C.Ref.ghost_read $&(use_sub));
    if (use_sub) {
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_subtract.func_subtract__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_subtract.func_subtract__fp) true true (Fp_shim.pre_of Funcptr_subtract.func_subtract__fp) (Fp_shim.post_of Funcptr_subtract.func_subtract__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (fun _ y -> y) Reassign_join_spec.wpre_sub Reassign_join_spec.wpost_sub);
        return subtract;
    } else {
        _ghost_stmt(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
        _ghost_stmt(Fp_shim.weaken (Fp_shim.of_fn_div _ _ Funcptr_add.func_add__fp) true true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp) (Reassign_join_spec.rj_pre (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (Reassign_join_spec.rj_post (Pulse.Lib.C.Casts.Bool.int32_to_bool g_use_sub)) (fun _ y -> y) Reassign_join_spec.wpre_add Reassign_join_spec.wpost_add);
        return add;
    }
}
#endif

/* A function pointer used as a return value (via `select_op`). */
int32_t return_fp(void)
    _ensures(return == 5)
{
    binop fp = select_op(0);
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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
    _unfold_uninit(struct ops, $&(o));
    o.op = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return o.op(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return u.op(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Function pointer stored via a heap pointer, then called. */
int32_t malloc_fp(void)
    _ensures(return == 5)
{
    int32_t (**pp)(int32_t, int32_t) =
        (int32_t (**)(int32_t, int32_t)) malloc(sizeof(int32_t (*)(int32_t, int32_t)));
    if (pp == NULL) {
        return 5;
    }
    *pp = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t r = (*pp)(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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
   `_old(*p)` needs the pointer's initial value threaded through the FuncPtr
   domain, which no longer exists (fnptr arguments are plain values only).
   Disabled until FuncPtr contracts support `_old` again.

void ptr_arg_cb(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    void (*f)(int32_t *) = inc;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_inc.func_inc__fp);
    f(p);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}
---- end DISABLED ptr_arg_cb ---- */

/* ---- DISABLED: storing a function pointer into an array element ----
   These four functions each write a function pointer into an array slot
   (`tbl[i] = add;`). Storing the large `of_fn_div ...` term directly makes
   `array_spec_upd s i (of_fn ...)` too large for the `array_spec_upd_*`
   SMTPats to fire, so the read-back can't recover `array_spec_mask`/
   `array_spec_initd`. This is an SMTPat matching issue, not a Z3 resource
   problem (confirmed: raising `z3rlimit` doesn't help). Disabled until
   `array_write`'s spec is made robust to large stored values.

int32_t assign_from_agg(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*fp)(int32_t, int32_t) = tbl[0];
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _fp_ghost(Fp_shim.valid_cast _ $(fp));
    return fp(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

int32_t use_array_slot(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*f)(int32_t, int32_t) = tbl[0];
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _fp_ghost(Fp_shim.valid_cast _ $(f));
    return f(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

int32_t array_runtime_idx(int32_t i)
    _requires(i == 0 || i == 1)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    tbl[1] = add;
    int32_t (*f)(int32_t, int32_t) = tbl[i];
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _fp_ghost(Fp_shim.valid_cast _ $(f));
    return f(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

int32_t multilayer(void)
    _ensures(return == 5)
{
    int32_t (*tbl[2])(int32_t, int32_t);
    tbl[0] = add;
    int32_t (*slot)(int32_t, int32_t) = tbl[0];
    struct ops o;
    _unfold_uninit(struct ops, $&(o));
    o.op = slot;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    _fp_ghost(Fp_shim.valid_cast _ $(slot));
    return o.op(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return o.op(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Ownership predicate for a `struct ops_c *` carrying `is_valid` on its `op`
   field, so `dispatch` can call through it. */
#ifdef PALOW
_include_pulse(Dispatch_spec,
  unfold let ops_c_valid ([@@@mkey] this: Pulse.Lib.C.Palow.Ptr.ptr) (vo: Struct_ops_c.struct_ops_c) : slprop =
    Struct_ops_c.struct_ops_c_pts_to this 1.0R vo **
    Fp_shim.is_valid vo.Struct_ops_c.fld_op true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp)
)
#else
_include_pulse(Dispatch_spec,
  unfold let ops_c_valid ([@@@mkey] this: ref Struct_ops_c.struct_ops_c) (vo: Struct_ops_c.struct_ops_c) : slprop =
    Pulse.Lib.Reference.pts_to this vo **
    Fp_shim.is_valid vo.Struct_ops_c.struct_ops_c__op true (Fp_shim.pre_of Funcptr_add.func_add__fp) (Fp_shim.post_of Funcptr_add.func_add__fp)
)
#endif

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
    _unfold_uninit(struct ops_c, $&(o));
    o.op = add;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    return dispatch(&o, 2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
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
    _unfold_uninit(struct vtable2, $&(v));
    v.bin = add;
    v.un = neg;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add.func_add__fp);
    int32_t s = v.bin(2, 3);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_neg.func_neg__fp);
    int32_t r = v.un(s);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
    return r;
}

/* ---- total function pointers & total->divergent weakening ---- */

/* A `_total` caller holding a pointer to the `_total` `add_t`: `of_fn_valid`
   seeds `is_valid .. false ..`, and the indirect call emits `call` (the
   total primitive). Total function pointers verify end-to-end. */
_total
int32_t use_total_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add_t;
#ifdef PALOW
/* Palow always reflects a C function as a possibly-divergent address: it
   infers divergence per body rather than taking it from `_total`, and the
   wrapper is written before any body is translated. So the total spellings
   below -- `of_fn_valid`, `pre_of_tot`, and the `false` validity bit -- become
   their divergent counterparts, and the weakening this section exercises runs
   from `true` to `true`. Recorded in palow.md as a known deviation. */
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_add_t.func_add_t__fp);
    return fp(2, 3);
#else
    _fp_ghost(Fp_shim.of_fn_valid _ _ Funcptr_add_t.func_add_t__fp);
    return fp(2, 3);
#endif
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Callback parameter expecting a POSSIBLY-DIVERGENT pointer (`is_valid .. true`).
   The body is divergent (default), so the indirect call emits `call_div`. */
int32_t apply_t(int32_t (*op)(int32_t, int32_t)
                    _refine((_slprop) _inline_pulse(
#ifdef PALOW
                        Fp_shim.is_valid $(this) true
                            (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp))),
#else
                        Fp_shim.is_valid $(this) true
                            (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp))),
#endif
                int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

/* Identity coercions plus a `weaken` from the total bit `false` to the divergent
   bit `true` (the `div ==> div'` refinement permits total->divergent). */
#ifdef PALOW
_include_pulse(Total_to_div_spec,
  ghost
  fn wpre_id (x: (Fp_shim.i32 & Fp_shim.i32))
             (y: erased Fp_shim.wit)
    requires (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) x y
    ensures (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) x y
  { () }

  ghost
  fn wpost_id (x: (Fp_shim.i32 & Fp_shim.i32))
               (y: erased Fp_shim.wit)
               (r: Fp_shim.i32)
    requires (Fp_shim.post_of Funcptr_add_t.func_add_t__fp) x y r
    ensures (Fp_shim.post_of Funcptr_add_t.func_add_t__fp) x y r
  { () }

  ghost
  fn weaken_t_to_div
       (f: Fp_shim.func_ptr
             (Fp_shim.i32 & Fp_shim.i32)
             Fp_shim.i32)
    requires Fp_shim.is_valid f true (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp)
    ensures Fp_shim.is_valid f true (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp)
  {
    Fp_shim.weaken f true true
      (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp)
      (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp)
      (fun _ y -> y)
      wpre_id
      wpost_id
  }
)
#else
_include_pulse(Total_to_div_spec,
  ghost
  fn wpre_id (x: (Fp_shim.i32 & Fp_shim.i32))
             (y: erased Fp_shim.wit)
    requires (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) x y
    ensures (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) x y
  { () }

  ghost
  fn wpost_id (x: (Fp_shim.i32 & Fp_shim.i32))
               (y: erased Fp_shim.wit)
               (r: Fp_shim.i32)
    requires (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp) x y r
    ensures (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp) x y r
  { () }

  ghost
  fn weaken_t_to_div
       (f: Fp_shim.func_ptr
             (Fp_shim.i32 & Fp_shim.i32)
             Fp_shim.i32)
    requires Fp_shim.is_valid f false (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp)
    ensures Fp_shim.is_valid f true (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp)
  {
    Fp_shim.weaken f false true
      (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp)
      (Fp_shim.pre_of_tot Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of_tot Funcptr_add_t.func_add_t__fp)
      (fun _ y -> y)
      wpre_id
      wpost_id
  }
)
#endif

/* Pass the TOTAL `add_t` to a callback that expects a possibly-divergent
   pointer: seed validity at `false`, `weaken` it up to `true`, then call. Shows
   that a total function pointer can be used where a divergent one is expected. */
int32_t weaken_total_to_div(void)
    _ensures(return == 5)
{
#ifdef PALOW
    _ghost_stmt(Fp_shim.of_fn_div_valid (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp) Funcptr_add_t.func_add_t__fp);
    _ghost_stmt(Total_to_div_spec.weaken_t_to_div _);
#else
    _fp_ghost(Fp_shim.of_fn_valid _ _ Funcptr_add_t.func_add_t__fp);
    _ghost_stmt(Total_to_div_spec.weaken_t_to_div _);
#endif
    return apply_t(add_t, 2, 3);
#ifdef PALOW
    /* Palow seeds its own copy of the validity at the decay site and drops
       that one itself; the copy seeded above for the `weaken` comes back out
       of the call and is dropped here. */
    _ghost_stmt(Fp_shim.drop_is_valid (Fp_shim.of_fn_div (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp) Funcptr_add_t.func_add_t__fp) (Fp_shim.pre_of Funcptr_add_t.func_add_t__fp) (Fp_shim.post_of Funcptr_add_t.func_add_t__fp));
#else
    _ghost_stmt(Fp_shim.drop_is_valid _ _ _);
#endif
}

/* Plain pointer parameter, no workaround annotations. Taking `touch`'s
   address forces a `__fp` wrapper via `pre_of`/`post_of` type-reflection;
   verifies because those take an explicit `erased c` witness parameter
   instead of a hidden implicit binder (which broke HOU with Error 189). */
void touch(int *p)
{
}

void use_touch_fp(void)
{
    void (*cb)(int *) = touch;
}

/* `struct itemx` verifies fine: `destroy`'s field type is a plain,
   non-recursive `func_ptr`, no self-reference, no strict-positivity error. */
struct itemx {
    void (*destroy)(struct itemx *self);
    unsigned int n;
};

/* `destroy_impl`'s `self` is `_consumes _allocated`: a real destructor that
   takes ownership of its receiver and frees it (same combo as
   `test/dpe/DPE.c`'s `destroy_uds_context`). */
void destroy_impl(_consumes _allocated struct itemx *self)
{
    free(self);
}

void use_destroy_impl_fp(void)
{
    void (*cb)(struct itemx *) = destroy_impl;
}

/* `Itemx_spec` is a separate module (not a field-level `_refine` on
   `destroy`) because `destroy_impl`'s spec module already depends on
   `struct itemx`; folding `is_valid` into the struct's own predicate would
   make `Struct_itemx` depend back on it, a circular module dependency
   (Error 308). */
#ifdef PALOW
_include_pulse(Itemx_spec,
  unfold let itemx_valid ([@@@mkey] this: Pulse.Lib.C.Palow.Ptr.ptr) (vo: Struct_itemx.struct_itemx) : slprop =
    Struct_itemx.struct_itemx_pts_to this 1.0R vo **
    Pulse.Lib.C.Palow.Alloc.freeable this Struct_itemx.struct_itemx_sizeof **
    Fp_shim.is_valid vo.Struct_itemx.fld_destroy true (Fp_shim.pre_of Funcptr_destroy_impl.func_destroy_impl__fp) (Fp_shim.post_of Funcptr_destroy_impl.func_destroy_impl__fp)
)
#else
_include_pulse(Itemx_spec,
  unfold let itemx_valid ([@@@mkey] this: ref Struct_itemx.struct_itemx) (vo: Struct_itemx.struct_itemx) : slprop =
    Pulse.Lib.Reference.pts_to this vo **
    Pulse.Lib.C.Ref.freeable this **
    Fp_shim.is_valid vo.Struct_itemx.struct_itemx__destroy true (Fp_shim.pre_of Funcptr_destroy_impl.func_destroy_impl__fp) (Fp_shim.post_of Funcptr_destroy_impl.func_destroy_impl__fp)
)
#endif

_type(itemx_val, Struct_itemx.struct_itemx)
_refine_value(itemx_val vo, _inline_pulse(Itemx_spec.itemx_valid $(this) $(vo)))
_plain
typedef struct itemx *itemx_ptr;

/* The same object, but only if there is one. `mk_itemx` allocates, so its
   result is the nullable spelling; `destroy_via_field` consumes an object that
   already exists, so it keeps the plain one. Palow alone: PAL's emitter states
   a nullable grant but has no way to spend it at a call site. */
_type(itemx_val, Struct_itemx.struct_itemx)
_refine_value(itemx_val vo, _inline_pulse(Itemx_spec.itemx_valid $(this) $(vo)))
_nullable _plain
typedef struct itemx *itemx_optr;

/* Self-dispatch through a field verifies once `self` is `_consumes`: a
   borrowed `self` opens two separate existentials for the same value
   (call-site witness vs. field-getter unfold), which Pulse can't unify
   (Error 228). Consuming `p` binds ONE existential both read from.
   `itemx_valid` also asserts `freeable`, for `destroy_impl`'s `free`.
   `drop_is_valid` clears the leftover non-affine `is_valid` fact. */
void destroy_via_field(_consumes itemx_ptr p) {
    p->destroy(p);
    _fp_ghost(Fp_shim.drop_is_valid _ _ _);
}

/* Constructs a valid `struct itemx` and RETURNS it, instead of consuming it
   immediately (see `destroy_via_field`). Mirrors `test/malloc/malloc.c`'s
   `mk_point`. `malloc`'s memory is genuinely uninitialized, so an explicit
   `$unfold-uninit` is needed before the field writes (unlike `vec_fam.c`'s
   `calloc`-based `vec_new`). */
#ifdef PALOW
itemx_optr mk_itemx(void)
#else
itemx_ptr mk_itemx(void)
#endif
{
    struct itemx *it = (struct itemx *) malloc(sizeof(struct itemx));
#ifdef PALOW
    if (it == NULL) {
        return NULL;
    }
#endif
    _unfold_uninit(struct itemx, $(it));
    it->destroy = destroy_impl;
    it->n = 0;
    _fp_ghost(Fp_shim.of_fn_div_valid _ _ Funcptr_destroy_impl.func_destroy_impl__fp);
    return it;
}

void use_mk_itemx(void)
{
    itemx_ptr it = mk_itemx();
#ifdef PALOW
    if (it == NULL) {
        return;
    }
#endif
    destroy_via_field(it);
}

/* ---- Multiple ownership groups across a function pointer ----
   Each callback below varies ONE thing: how many parameters contribute an
   ownership group (a requires-side existential). Parameter count is held
   separate from group count on purpose, so a failure can be attributed to
   one or the other.

     mo_one    1 owned param              -> 1 group
     mo_scalar 2 params, 1 pointer        -> 1 group (a by-value scalar
                                             emits no existential binder)
     mo_two    2 owned params             -> 2 groups
     mo_three  3 owned params             -> 3 groups

   Every address-taken function gets a `Funcptr_<g>` wrapper whose
   requires-side ownership is carried by ONE explicit `y_fp: erased c`
   witness parameter, with each group's props recovered by projecting out of
   it (see emit.rs `emit_fnptr_spec_core`). `mo_one`/`mo_scalar` are the
   controls for that machinery at one group; `mo_two`/`mo_three` exercise it
   at two and three. */

struct mo_a { int32_t x; };
struct mo_b { int32_t y; };

int32_t mo_one(struct mo_a *p)
    _ensures(return == p->x)
{
    return p->x;
}

int32_t mo_scalar(struct mo_a *p, int32_t k)
    _requires(p->x > 0 && p->x < 100 && k > 0 && k < 100)
{
    return p->x + k;
}

int32_t mo_two(struct mo_a *p, struct mo_b *q)
    _requires(p->x > 0 && p->x < 100 && q->y > 0 && q->y < 100)
{
    return p->x + q->y;
}

int32_t mo_three(struct mo_a *p, struct mo_b *q, struct mo_a *r)
    _requires(p->x > 0 && p->x < 100 && q->y > 0 && q->y < 100
              && r->x > 0 && r->x < 100)
{
    return p->x + q->y + r->x;
}

/* Address-taken through a const ops table — the shape real drivers use. */
struct mo_ops {
    int32_t (*f1)(struct mo_a *);
    int32_t (*fs)(struct mo_a *, int32_t);
    int32_t (*f2)(struct mo_a *, struct mo_b *);
    int32_t (*f3)(struct mo_a *, struct mo_b *, struct mo_a *);
};

const struct mo_ops the_mo_ops = {
    .f1 = mo_one, .fs = mo_scalar, .f2 = mo_two, .f3 = mo_three
};

/* Framing a call is different from framing a function pointer's validity.
   Both contracts use the same witness type; 42 is an arbitrary fixed
   pointee value, so witness conversion is not involved in this example.

   Old model only for now: Palow's `FnPtr` has no `frame` axiom yet, and the
   contracts below are written against Pulse references rather than addresses.
   Porting it is on the Palow backlog. */
#ifndef PALOW
_include_pulse(Fp_frame_spec,
  unfold let plain_pre (p: ref Int32.t) (w: erased unit) : slprop = emp
  unfold let plain_post (p: ref Int32.t) (w: erased unit) (r: unit) : slprop = emp

  unfold let framed_pre (p: ref Int32.t) (w: erased unit) : slprop =
    Pulse.Lib.Reference.pts_to p 42l
  unfold let framed_post (p: ref Int32.t) (w: erased unit) (r: unit) : slprop =
    Pulse.Lib.Reference.pts_to p 42l

  ghost fn frame_wpre (p: ref Int32.t) (w: erased unit)
    requires framed_pre p w
    ensures plain_pre p w ** framed_pre p w
  { () }

  ghost fn frame_wpost (p: ref Int32.t) (w: erased unit) (r: unit)
    requires plain_post p w r ** framed_pre p w
    ensures framed_post p w r
  { () }

  ghost fn frame_plain (f: Pulse.Lib.C.FuncPtr.func_ptr (ref Int32.t) unit)
    requires Pulse.Lib.C.FuncPtr.is_valid f true plain_pre plain_post
    ensures Pulse.Lib.C.FuncPtr.is_valid f true framed_pre framed_post **
            Pulse.Lib.C.FuncPtr.is_valid f true plain_pre plain_post
  {
    unfold (Pulse.Lib.C.FuncPtr.is_valid f true plain_pre plain_post);
    fold (Pulse.Lib.C.FuncPtr.is_valid f true plain_pre plain_post);
    Pulse.Lib.C.FuncPtr.frame f true plain_pre plain_post framed_pre;
    Pulse.Lib.C.FuncPtr.weaken f true true
      (fun p w -> plain_pre p w ** framed_pre p w)
      (fun p w r -> plain_post p w r ** framed_pre p w)
      framed_pre framed_post (fun _ w -> w) frame_wpre frame_wpost;
    fold (Pulse.Lib.C.FuncPtr.is_valid f true plain_pre plain_post);
  }
)

/* Control: ordinary call-site framing preserves the pointee. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) 42l))
void fp_frame_direct(
    void (*f)(_plain int *p)
        _refine((_slprop) _inline_pulse(
            Pulse.Lib.C.FuncPtr.is_valid $(this) true
                Fp_frame_spec.plain_pre Fp_frame_spec.plain_post)),
    _plain int *p)
{
    f(p);
}

/* Control: a consumer with the framed validity can call its pointer. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) 42l))
void fp_frame_consumer(
    void (*f)(_plain int *p)
        _refine((_slprop) _inline_pulse(
            Pulse.Lib.C.FuncPtr.is_valid $(this) true
                Fp_frame_spec.framed_pre Fp_frame_spec.framed_post)),
    _plain int *p)
{
    f(p);
}

/* Adapt the same arbitrary pointer's validity using the frame axiom.
   Without this ghost step the consumer call fails with Error 19.
   FuncPtr.weaken alone cannot carry a resource between its two coercions. */
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) 42l))
void fp_frame_adapt(
    void (*f)(_plain int *p)
        _refine((_slprop) _inline_pulse(
            Pulse.Lib.C.FuncPtr.is_valid $(this) true
                Fp_frame_spec.plain_pre Fp_frame_spec.plain_post)),
    _plain int *p)
{
    _ghost_stmt(Fp_frame_spec.frame_plain $(f));
    fp_frame_consumer(f, p);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid $(f)
      Fp_frame_spec.framed_pre Fp_frame_spec.framed_post);
}
#endif

uint32_t global_live_counter;

/* Ghost-indexed ownership relates entry and exit values without `_old` or
 * mutable entry equalities in the function-pointer postcondition guard. */
_ghost_arg(uint32_t before)
void global_live_bump(void)
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(&global_live_counter) $(before)))
    _requires(before < 100)
    _ensures(_live(global_live_counter))
    _ensures(global_live_counter == before + 1)
{
    global_live_counter = global_live_counter + 1;
}

_ghost_arg(uint32_t before)
void global_live_call(void)
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(&global_live_counter) $(before)))
    _requires(before < 100)
    _ensures(_live(global_live_counter))
    _ensures(global_live_counter == before + 1)
{
    void (*fp)(void) = global_live_bump;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_global_live_bump.func_global_live_bump__fp);
    fp();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Keep direct _live coverage with a fixed-value postcondition. */
void global_live_set(void)
    _requires(_live(global_live_counter))
    _ensures(_live(global_live_counter))
    _ensures(global_live_counter == 42)
{
    global_live_counter = 42;
}

void global_live_set_call(void)
    _requires(_live(global_live_counter))
    _ensures(_live(global_live_counter))
    _ensures(global_live_counter == 42)
{
    global_live_counter = 10;
    void (*fp)(void) = global_live_set;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_global_live_set.func_global_live_set__fp);
    fp();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Snapshot both globals and the updated pointee; preserve q's saved value. */
uint32_t global_live_left;
uint32_t global_live_right;

_ghost_arg(uint32_t before_left)
_ghost_arg(uint32_t before_right)
_ghost_arg(uint32_t before_p)
_ghost_arg(uint32_t saved)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(saved)))
void global_live_mixed(_plain uint32_t *p, _plain uint32_t *q)
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(&global_live_left) $(before_left)))
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(&global_live_right) $(before_right)))
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) $(before_p)))
    _requires(before_left < 100)
    _requires(before_right < 100)
    _requires(before_p < 100)
    _ensures(_live(global_live_left) && _live(global_live_right))
    _ensures(_live(*p))
    _ensures(global_live_left == before_left + 1)
    _ensures(global_live_right == before_right + 1)
    _ensures(*p == before_p + 1)
{
    global_live_left = global_live_left + 1;
    global_live_right = global_live_right + 1;
    *p = *p + 1;
}

_ghost_arg(uint32_t before_left)
_ghost_arg(uint32_t before_right)
_ghost_arg(uint32_t before_p)
_ghost_arg(uint32_t saved)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(saved)))
void global_live_mixed_call(_plain uint32_t *p, _plain uint32_t *q)
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(&global_live_left) $(before_left)))
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(&global_live_right) $(before_right)))
    _requires(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) $(before_p)))
    _requires(before_left < 100)
    _requires(before_right < 100)
    _requires(before_p < 100)
    _ensures(_live(global_live_left) && _live(global_live_right))
    _ensures(_live(*p))
    _ensures(global_live_left == before_left + 1)
    _ensures(global_live_right == before_right + 1)
    _ensures(*p == before_p + 1)
{
    void (*fp)(_plain uint32_t *, _plain uint32_t *) = global_live_mixed;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_global_live_mixed.func_global_live_mixed__fp);
    fp(p, q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Distinct values expose swapped witnesses and vacuous postconditions. */
void global_live_distinct(void)
    _requires(_live(global_live_left) && _live(global_live_right))
    _ensures(_live(global_live_left) && _live(global_live_right))
    _ensures(global_live_left == 11 && global_live_right == 21)
{
    global_live_left = 10;
    global_live_right = 20;
    uint32_t p = 30;
    uint32_t q = 40;
    void (*fp)(_plain uint32_t *, _plain uint32_t *) = global_live_mixed;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_global_live_mixed.func_global_live_mixed__fp);
    fp(&p, &q);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    _assert(p == 31 && q == 40);
}

#if 0

/* [DEFERRED] Indirect recursion through a function pointer. Taking the
   address of the function under definition decays to `of_fn ..
   func_rec_via_ptr__fp`, but PAL emits the function and its lifted triple
   as two separate top-level `fn`s (not a `fn rec .. and ..` group), so the
   reference is forward (F* Error 72). Needs an emitter change to emit both
   as one mutually-recursive group. */
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
