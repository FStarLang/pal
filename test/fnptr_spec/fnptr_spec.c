#include "pal.h"
#include <stdint.h>

/* Indirect calls where an argument's struct has a `__spec` companion --
   https://github.com/FStarLang/pal/issues/277.

   A struct with a pointer field gets an `[@@erasable]` `struct_X__spec`, so an
   owned `struct X *` parameter contributes *two* elim components to the
   witness, not one. The call site emits `_` for the whole witness and Pulse
   infers it. */

/* Control: no pointer field, so no `__spec`. One elim component. */
struct plain {
  int32_t x;
};

int32_t impl_ok(struct plain *q) { return 1; }

struct ops_ok {
  int32_t (*get)(struct plain *q);
};

static const struct ops_ok o_ok = {.get = impl_ok};

int32_t call_ok(struct plain *q)
{
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_ok.func_impl_ok__fp);
  _ghost_stmt(Global_o_ok.acquire_var_o_ok ());
  const struct ops_ok *p = &o_ok;
  return p->get(q);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
  _ghost_stmt(drop_ (exists* fr. pts_to Global_o_ok.addr_var_o_ok #fr _));
}

/* The issue's reproducer. `y` gives `struct dep` a `__spec`, so the witness is
   `((struct_dep & struct_dep__spec) & unit)`. */
struct dep {
  int32_t x;
  int32_t *y;
};

int32_t impl_dep(struct dep *d) { return 1; }

struct ops {
  int32_t (*get)(struct dep *d);
};

static const struct ops o = {.get = impl_dep};

int32_t call_dep(struct dep *d)
{
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_dep.func_impl_dep__fp);
  _ghost_stmt(Global_o.acquire_var_o ());
  const struct ops *p = &o;
  return p->get(d);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
  _ghost_stmt(drop_ (exists* fr. pts_to Global_o.addr_var_o #fr _));
}

/* Every kind of witness component at once: `d` gives two elim leaves (value and
   `__spec`), `a` one, and the `_ghost_arg` one ghost leaf, so

     c = ((struct_dep & (struct_dep__spec & ty_int32_t)) & ty_int32_t)

   the first case here where both halves are non-trivial and one argument
   contributes more than one leaf. */
_ghost_arg(int32_t v)
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R $(v)))
int32_t impl_mixed(struct dep *d, int32_t *a, _plain int32_t *q)
{
  return *a;
}

/* The `m` field carries `is_valid` as a field-level `_refine`. */
struct ops_mixed {
  _refine((_slprop) _inline_pulse(
      Pulse.Lib.C.FuncPtr.is_valid $(this) true
        (Pulse.Lib.C.FuncPtr.pre_of Funcptr_impl_mixed.func_impl_mixed__fp)
        (Pulse.Lib.C.FuncPtr.post_of Funcptr_impl_mixed.func_impl_mixed__fp)))
  int32_t (*m)(struct dep *d, int32_t *a, _plain int32_t *q);
};

static const struct ops_mixed o_m = {.m = impl_mixed};

/* A global's `acquire` yields a bare `pts_to` at the global's value, not the
   struct's `__pred`, so the field refinement is not in scope here. It costs
   nothing to reintroduce: `o_m.m` is definitionally `of_fn_div .. impl_mixed`,
   so `of_fn_div_valid` supplies the `is_valid` from `emp`. */
_requires(*a > 0 && *a < 100)
_preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(q) #1.0R 0l))
int32_t call_mixed(struct dep *d, int32_t *a, _plain int32_t *q)
{
  _ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_div_valid _ _ Funcptr_impl_mixed.func_impl_mixed__fp);
  _ghost_stmt(Global_o_m.acquire_var_o_m ());
  const struct ops_mixed *p = &o_m;
  return p->m(d, a, q);
  _ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _);
  _ghost_stmt(drop_ (exists* fr. pts_to Global_o_m.addr_var_o_m #fr _));
}

/* A struct-level `_refine` that reads an `_array` field's `_length`, on a
   function whose address is taken. The refinement becomes a `pure` conjunct
   inside the wrapper's witness pattern `let`, so it may not name a ghost fn:
   `_length` is emitted as the pure projection `array_spec_len` of the
   predicate's spec record rather than as a `length_of` call. */
struct cell {
  int v;
};

struct _refine(this.arr._length == 4) _refine(this.brr._length == 4) box {
  _array struct cell *arr;
  _array struct cell *brr;
};

void use(struct box *b) {}

struct ops_arr {
  void (*fn)(struct box *b);
};

static const struct ops_arr o_arr = {.fn = use};

/* The same, with the struct passed *by value*. This is the sharper case: with
   no `pts_to` to eliminate, the witness's elim half is just the `__spec`, so
   the refinement conjuncts mention only `x_fp` -- a plain parameter -- and no
   witness binding at all. They are still constrained by sitting inside the
   pattern `let`, which is what makes the ghost fn unusable there. */
void use_byval(struct box b) {}

struct ops_byval {
  void (*fn)(struct box b);
};

static const struct ops_byval o_byval = {.fn = use_byval};
