#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* ==========================================================================
 * Function-pointer tests against the axiomatized Pulse.Lib.C.FuncPtr library.
 * Every example here verifies (`make -C test/func_pointer`); the single deferred
 * case (`rec_via_ptr`) is kept under `#if 0` at the end.
 *
 * Indirect-call recipe: a call `fp(x)` emits `call _ _ (!fp) args` with the spec
 * left as inference holes. For a pointer holding a concrete `of_fn ..` (a decayed
 * named function), seed the validity fact just before the call with
 * `_ghost_stmt(.. of_fn_valid ..)`. `call` returns `is_valid` in its
 * postcondition (validity is a persistent pure fact), so a caller that does not
 * itself export validity drops the surplus afterwards with
 * `_ghost_stmt(.. drop_is_valid _ _ _)`. Callback parameters instead export
 * `is_valid` via a `_refine` refinement and keep the returned fact.
 * ========================================================================== */

/* ---- shared helper callees ---- */

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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Explicit address-of `&`. */
int32_t use_amp(void)
    _ensures(return == 7)
{
    int32_t (*fp)(int32_t, int32_t) = &add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(3, 4);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Transitive copy from another pointer. */
int32_t use_transitive(void)
    _ensures(return == 5)
{
    int32_t (*fp1)(int32_t, int32_t) = add;
    int32_t (*fp2)(int32_t, int32_t) = fp1;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp2(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Straight-line reassignment: the same pointer, different targets per call. */
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

/* Reassignment through a copy of another pointer. */
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

/* ---- type spellings ---- */

/* Inline declarator type. */
int32_t use_inline_declarator(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* `typedef`'d function-pointer type. */
int32_t use_typedef(void)
    _ensures(return == 5)
{
    binop fp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Const-qualified parameter types (qualifiers ignored). */
int32_t qualified_params(void)
    _ensures(return == 5)
{
    int32_t (*fp)(const int32_t, const int32_t) = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* A function type (not a pointer) that decays to a pointer. */
int32_t func_type_decay(void)
    _ensures(return == 5)
{
    binop_fn *fp = add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return fp(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Cast between compatible function-pointer types. */
int32_t use_cast(void)
    _ensures(return == 5)
{
    binop fp = (binop) add;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
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

/* ---- calling: arities / void ---- */

/* Zero-arg / `void`-return callback. */
void use_void_cb(void)
{
    void (*cb)(void) = do_nothing;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_do_nothing.func_do_nothing_pre Func_do_nothing.func_do_nothing_post Func_do_nothing.func_do_nothing__fp);
    cb();
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-1 call. */
int32_t use_arity1(void)
    _ensures(return == -5)
{
    int32_t (*g)(int32_t) = neg;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_neg.func_neg_pre Func_neg.func_neg_post Func_neg.func_neg__fp);
    return g(5);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-3 call, mixed-width tuple. */
uint32_t use_arity3(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_combine.func_combine_pre Func_combine.func_combine_post Func_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-3 call, mixed-width tuple, with `&`. */
uint32_t use_arity3_amp(void)
    _ensures(return == 15)
{
    uint32_t (*fp3)(uint8_t, uint32_t, int32_t) = &combine;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_combine.func_combine_pre Func_combine.func_combine_post Func_combine.func_combine__fp);
    return fp3(5, 10, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
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

/* Pointer-to-function-pointer. */
int32_t ptr_to_fp(void)
    _ensures(return == 5)
{
    int32_t (*fp)(int32_t, int32_t) = add;
    int32_t (**pp)(int32_t, int32_t) = &fp;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return (*pp)(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* ---- callback parameters (abstract func_ptr params) ----
   The pointer is a func_ptr PARAMETER, so the caller supplies the `is_valid`
   fact via a `_refine((_slprop) is_valid $(this) ..)` refinement on the
   parameter, landing it in both the generated `requires` and `ensures`. */

/* Function pointer as a callback parameter. */
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

/* Passing concrete `add` to the callback. */
int32_t use_apply_add(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return apply(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Arity-1 callback parameter. */
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

/* Passing concrete `neg` to the arity-1 callback. */
int32_t use_apply_neg(void)
    _ensures(return == -5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_neg.func_neg_pre Func_neg.func_neg_post Func_neg.func_neg__fp);
    return apply1(neg, 5);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Callback parameter typed via the `binop` typedef. */
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

/* Typedef'd callback-parameter call site. */
int32_t typedef_callback(void)
    _ensures(return == 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return apply_typedef(add, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* `apply_weaker` takes a callback whose declared post (`aw_post`) is WEAKER than
   `subtract` provides. `weaken_sub_to_aw` moves subtract's validity onto the
   weaker spec (identity pre-coercion; post-coercion proving
   `return == a - b ==> return < a` under the shared precondition). */
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

/* Callback declared with a weaker postcondition than `subtract` provides. */
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

/* Pass `subtract` to the weaker callback: seed validity, `weaken`, then call. */
int32_t weaken_callback(void)
    _ensures(return < 5)
{
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_subtract.func_subtract_pre Func_subtract.func_subtract_post Func_subtract.func_subtract__fp);
    _ghost_stmt(Apply_weaker_spec.weaken_sub_to_aw _);
    return apply_weaker(subtract, 5, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* `_nullable` callback: validity is wrapped in `unless_null`; the `if (fp)`
   branch elims it to `is_valid` for the call and intros it back afterwards. */
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

/* `fp` is `subtract` or `add` by a runtime guard, then called across the join. */
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

/* Same as `reassign_join`, with the call after the join. */
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

/* Returns a runtime-chosen pointer, its validity threaded out through a
   guard-keyed `_ensures`. Written as explicit `if`/`else` so each arm has a
   source site to seed `of_fn_valid` and `weaken` onto the guard-keyed spec. */
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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    int32_t r = (*pp)(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
    free(pp);
    return r;
}

/* Pointer/ownership callee, for ptr_arg_cb. */
void inc(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    *p = *p + 1;
}

/* Pointer/ownership argument threaded through an indirect call: the callee's
   relational `*p == _old(*p) + 1` is carried by threading the pointer's initial
   pointee value through the FuncPtr domain (see emit.rs `fnptr_domain_with_old`). */
void ptr_arg_cb(int32_t *p)
    _requires(*p < 100)
    _ensures(*p == _old(*p) + 1)
{
    void (*f)(int32_t *) = inc;
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_inc.func_inc_pre Func_inc.func_inc_post Func_inc.func_inc__fp);
    f(p);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Read a function pointer out of an array element into a local, then call it. */
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

/* Function pointer stored in a fixed-array slot, read back, and called;
   `valid_cast` re-keys the validity fact to the read-back value. */
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

/* Array indexed by a runtime value (both slots hold `add`, index in {0,1}), so
   the read-back value is only provably `add`; `valid_cast` re-keys its validity. */
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

/* Function pointer threaded array element -> struct field before the call
   (combines the array `valid_cast` and struct-unfold recipes). */
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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return o.op(2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

/* Ownership predicate for a `struct ops_c *` carrying `is_valid` on its `op`
   field, so `dispatch` can call through it. */
_include_pulse(Dispatch_spec,
  unfold let ops_c_valid ([@@@mkey] this: ref Struct_ops_c.struct_ops_c) (vo: Struct_ops_c.struct_ops_c) : slprop =
    Pulse.Lib.Reference.pts_to this vo **
    Pulse.Lib.C.FuncPtr.is_valid vo.Struct_ops_c.struct_ops_c__op Func_add.func_add_pre Func_add.func_add_post
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
    _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_add.func_add_pre Func_add.func_add_post Func_add.func_add__fp);
    return dispatch(&o, 2, 3);
    _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
}

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
